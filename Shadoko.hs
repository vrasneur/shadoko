{-# OPTIONS_GHC -fglasgow-exts #-}

{-
 -   Shadoko.hs --- Interpreter for the Shadoko language
 -   Copyright (c) 2008 Vincent Rasneur <vrasneur@free.fr>
 -
 -   Compile with: ghc -O2 --make -o shadoko Shadoko.hs
 -
 -   This program is free software; you can redistribute it and/or modify
 -   it under the terms of the GNU General Public License as published by
 -   the Free Software Foundation; version 3 only.
 -
 -   This program is distributed in the hope that it will be useful,
 -   but WITHOUT ANY WARRANTY; without even the implied warranty of
 -   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 -   GNU General Public License for more details.
 -
 -   You should have received a copy of the GNU General Public License
 -   along with this program; if not, write to the Free Software
 -   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 -}

import Control.Monad
import Control.Monad.State
import Data.Bits (shiftR)
import Data.Char (chr, ord, toUpper)
import Data.List (sort, genericIndex, genericLength, genericDrop, genericTake)
import Data.Maybe (fromJust)
import System.Directory (doesFileExist, getPermissions, readable)
import System.Environment (getArgs)
import System.Exit
import System.IO
import qualified Data.Set as Set

erreur :: String -> IO ()
erreur msg = do hPutStrLn stderr $ "Erreur : " ++ msg
                exitWith $ ExitFailure $ -1

erreurGuard :: String -> Bool -> IO ()
erreurGuard _ True = return ()
erreurGuard msg False = erreur msg

type EtatDeShadokoVal = StateT Shadoko IO

type EtatDeShadoko = EtatDeShadokoVal ()

data Mot = GA | BU | ZO | MEU
           deriving (Eq, Ord, Show)

class Shadok a where
    toShadok :: a -> Mot
    fromShadok :: Mot -> a

instance Shadok String where
    toShadok "GA" = GA
    toShadok "BU" = BU
    toShadok "ZO" = ZO
    toShadok "MEU" = MEU
    fromShadok GA = "GA"
    fromShadok BU = "BU"
    fromShadok ZO = "ZO"
    fromShadok MEU = "MEU"

instance Shadok Int where
    toShadok 0 = GA
    toShadok 1 = BU
    toShadok 2 = ZO
    toShadok 3 = MEU
    fromShadok GA = 0
    fromShadok BU = 1
    fromShadok ZO = 2
    fromShadok MEU = 3

data Poubelles a = Poubelle a
                 | GrandePoubelle (Poubelles a)
                   deriving (Eq, Ord, Show)

data Nombre = Moins Nombre
            | PasPoubelle Mot
            | Decharge (Set.Set (Poubelles Mot)) Mot
              deriving (Eq, Ord)

instance Enum Nombre where
    toEnum n | n < 0 && n /= minBound = Moins $ toEnum (- n)
             | n >= 0 && n < 4 = PasPoubelle $ toShadok n
    toEnum n = (if n == minBound then Moins else id) $
               Decharge (creePoubelles Set.empty) (toShadok (n `mod` 4))
        where creePoubelles s | 4 ^ ((Set.size s) + 1) > (abs $ toInteger n) = s
              creePoubelles s = let len = Set.size s
                                    val = (n `shiftR` ((len + 1) * 2)) `mod` 4
                                in creePoubelles (Set.insert
                                                  (creePoubelle len
                                                   (Poubelle (toShadok val))) s)
              creePoubelle 0 p = p
              creePoubelle r p = creePoubelle (r - 1) (GrandePoubelle p)
    fromEnum (Moins x) = - (fromEnum x)
    fromEnum (PasPoubelle x) = fromShadok x
    fromEnum (Decharge s x) = (Set.fold comptePoubelles (fromShadok x) s)
        where comptePoubelles p n = n + (comptePoubelle p 1)
              comptePoubelle (Poubelle x) acc = acc * 4 * (fromShadok x)
              comptePoubelle (GrandePoubelle x) acc = comptePoubelle x (acc * 4)

auPluriel :: Mot -> String -> String
auPluriel GA s = s
auPluriel BU s = s
auPluriel _ s = s ++ "s"

instance Show Nombre where
    show (Moins x) = "moins " ++ (show x)
    show (PasPoubelle x) = (fromShadok x) ++ "\n"
    show (Decharge set x) = ((foldl showPoubelles "" (sort $ Set.toList set)) ++
                             (fromShadok x) ++ "\n")
        where showPoubelles str p = (showPoubelle p "") ++ str
              showPoubelle (Poubelle x) s =
                  (fromShadok x) ++ " " ++ s ++ (auPluriel x "poubelle") ++ " "
              showPoubelle (GrandePoubelle p@(Poubelle x)) s =
                  showPoubelle p (s ++ (auPluriel x "grande") ++ " ")
              showPoubelle (GrandePoubelle p) s = showPoubelle p (s ++ "tres ")

data Pompe = Reservoir Nombre
           deriving (Show)

creePompe :: Pompe
creePompe = Reservoir $ PasPoubelle GA

pompeUnCoup :: Pompe -> Pompe
pompeUnCoup (Reservoir x) = Reservoir $ succ x

depompeUnCoup :: Pompe -> Pompe
depompeUnCoup (Reservoir x) = Reservoir $ pred x

data Pompes = Pompes { courante :: Pompe
                     , gauche :: [Pompe]
                     , droite :: [Pompe] }
              deriving (Show)

creePompes :: Pompes
creePompes = Pompes { courante = creePompe
                    , gauche = []
                    , droite = [] }

vaAGauche :: Pompes -> Pompes
vaAGauche ps@(Pompes{gauche=[]}) =
    Pompes { courante = creePompe
           , gauche = []
           , droite = (courante ps):(droite ps) }
vaAGauche ps =
    let ancGauche = gauche ps
    in Pompes { courante = head ancGauche
              , gauche = drop 1 ancGauche
              , droite = (courante ps):(droite ps) }

vaADroite :: Pompes -> Pompes
vaADroite ps@(Pompes{droite=[]}) =
    Pompes { courante = creePompe
           , gauche = (courante ps):(gauche ps)
           , droite = [] }
vaADroite ps =
    let ancDroite = droite ps
    in Pompes { courante = head ancDroite
              , gauche = (courante ps):(gauche ps)
              , droite = drop 1 ancDroite }

inverseGaucheDroite :: Pompes -> Pompes
inverseGaucheDroite ps = ps{ droite = gauche ps
                           , gauche = droite ps }

data Shadoko = Shadoko { mode :: Maybe Mot
                       , borne :: Integer
                       , boucles :: [Integer]
                       , mots :: [Mot]
                       , pompes :: Pompes }

creeShadoko :: [Mot] -> Shadoko
creeShadoko mots' = Shadoko { mode = Nothing
                            , borne = 0
                            , boucles = []
                            , mots = mots'
                            , pompes = creePompes }

pompeCourante :: Shadoko -> Pompe
pompeCourante shadoko = courante $ pompes shadoko

regardeInstruction :: EtatDeShadokoVal Mot
regardeInstruction = do
  shadoko <- get
  return (mots shadoko `genericIndex` borne shadoko)

regardeReservoirPompeCourante :: EtatDeShadokoVal Nombre
regardeReservoirPompeCourante = do
  (Reservoir nb) <- get >>= return . pompeCourante
  return nb

toucheARien :: Nombre -> String 
toucheARien = show

enCaractere :: Nombre -> String 
enCaractere nb = [chr $ (fromEnum nb) `mod` 256]

montreReservoirPompeCourante :: (Nombre -> String) -> EtatDeShadoko
montreReservoirPompeCourante conv = do
  nb <- regardeReservoirPompeCourante
  liftIO $ (putStr $ conv nb) >> hFlush stdout

changeReservoirPompeCourante :: EtatDeShadoko
changeReservoirPompeCourante = do
  ch <- liftIO $ getChar
  modify (\s -> s{pompes = (pompes s){courante = Reservoir $ toEnum $ ord ch}})

glande :: EtatDeShadoko
glande = return ()

avanceUnCoup :: EtatDeShadoko
avanceUnCoup = modify (\s -> s{borne = (borne s) + 1})

avanceJusqueLa :: Integer -> EtatDeShadoko
avanceJusqueLa val = modify (\s -> s{borne = val})

agitPompeCourante :: (Pompe -> Pompe) -> EtatDeShadoko
agitPompeCourante fun = 
    modify (\s -> s{pompes = (pompes s){courante = fun $ pompeCourante s}})

agitPompes :: (Pompes -> Pompes) -> EtatDeShadoko
agitPompes fun = modify (\s -> s{pompes = fun $ pompes s})

changeMode :: Maybe Mot -> EtatDeShadoko
changeMode mode' = modify (\s -> s{mode = mode'})

annuleMode :: EtatDeShadoko
annuleMode = changeMode Nothing

chercheDebutBoucle :: EtatDeShadokoVal Integer
chercheDebutBoucle = do
  shadoko <- get
  let boucles' = boucles shadoko
  when (null boucles')
           (liftIO $ erreur "Pas de debut de boucle !")
  return $ head boucles'

vaDebutBoucle :: EtatDeShadoko
vaDebutBoucle = chercheDebutBoucle >>= avanceJusqueLa

trouveFinBoucle :: Maybe Mot -> [Mot] -> Integer -> Integer -> Maybe Integer
trouveFinBoucle _ [] _ _ = Nothing
trouveFinBoucle (Just MEU) (BU:_) n 0 = Just n
trouveFinBoucle m@(Just MEU) (GA:xs) n s = trouveFinBoucle m xs (n + 1) (s + 1)
trouveFinBoucle m@(Just MEU) (BU:xs) n s = trouveFinBoucle m xs (n + 1) (s - 1)
trouveFinBoucle (Just _) (MEU:xs) n s = trouveFinBoucle Nothing xs (n + 1) s
trouveFinBoucle m@(Just _) (_:xs) n s = trouveFinBoucle m xs (n + 1) s
trouveFinBoucle Nothing (x:xs) n s = trouveFinBoucle (Just x) xs (n + 1) s

chercheFinBoucle :: EtatDeShadokoVal Integer
chercheFinBoucle = do
  shadoko <- get
  let (mode', borne') = (mode shadoko, borne shadoko)
  instruction <- regardeInstruction
  let level = if (mode' == Just MEU && instruction == GA) then -1 else 0
  let val = trouveFinBoucle mode' (genericDrop borne' $ mots shadoko) borne' level
  when (val == Nothing)
           (liftIO $ erreur "Pas de fin de boucle !")
  return (fromJust val)

vaFinBoucle :: EtatDeShadoko
vaFinBoucle = chercheFinBoucle >>= avanceJusqueLa

trouveDebutBoucles :: Maybe Mot -> [Mot] -> Integer -> [Integer] -> [Integer]
trouveDebutBoucles _ [] _ acc = acc
trouveDebutBoucles m@(Just MEU) (GA:xs) n acc =
    trouveDebutBoucles m xs (n + 1) (n:acc)
-- ignorer les erreurs pour les fins de boucle sans debut
trouveDebutBoucles m@(Just MEU) (BU:xs) n [] =
    trouveDebutBoucles m xs (n + 1) []
trouveDebutBoucles m@(Just MEU) (BU:xs) n (_:bs) =
    trouveDebutBoucles m xs (n + 1) bs
trouveDebutBoucles (Just _) (MEU:xs) n acc =
    trouveDebutBoucles Nothing xs (n + 1) acc
trouveDebutBoucles m@(Just _) (_:xs) n acc =
    trouveDebutBoucles m xs (n + 1) acc
trouveDebutBoucles Nothing (x:xs) n acc =
    trouveDebutBoucles (Just x) xs (n + 1) acc

inverseSens :: EtatDeShadoko
inverseSens = do
  shadoko <- get
  let mots' = reverse $ mots shadoko
  let borne' = genericLength mots' - (borne shadoko) - 1
  let boucles' = trouveDebutBoucles Nothing (genericTake (borne' + 1) mots') 0 []
  modify (\s -> s{mots = mots', borne = borne', boucles = boucles'})

ajouteBoucle :: EtatDeShadoko
ajouteBoucle = modify (\s -> s{boucles = (borne s):(boucles s)})

retireBoucle :: EtatDeShadoko
retireBoucle = modify (\s -> s{boucles = tail $ boucles s})

interprete :: EtatDeShadoko
interprete = do
  shadoko <- get
  case mode shadoko of
    Nothing -> modage
    (Just GA) -> pompage
    (Just BU) -> choisissage
    (Just ZO) -> interactionnage
    (Just MEU) -> bouclage
  newshadoko <- get
  when ((borne newshadoko) < (genericLength $ mots newshadoko))
           (interprete)

modage :: EtatDeShadoko
modage = do
  regardeInstruction >>= changeMode . Just
  avanceUnCoup

pompage :: EtatDeShadoko
pompage = do
  instruction <- regardeInstruction
  case instruction of
    GA -> agitPompeCourante depompeUnCoup
    BU -> agitPompeCourante pompeUnCoup
    ZO -> glande
    MEU -> annuleMode
  avanceUnCoup

choisissage :: EtatDeShadoko
choisissage = do
  instruction <- regardeInstruction
  case instruction of
    GA -> agitPompes vaAGauche
    BU -> agitPompes vaADroite
    ZO -> agitPompes inverseGaucheDroite
    MEU -> annuleMode
  avanceUnCoup

interactionnage :: EtatDeShadoko
interactionnage = do
  instruction <- regardeInstruction
  case instruction of
    GA -> montreReservoirPompeCourante toucheARien
    BU -> montreReservoirPompeCourante enCaractere
    ZO -> changeReservoirPompeCourante
    MEU -> annuleMode
  avanceUnCoup

bouclage :: EtatDeShadoko
bouclage = do
  instruction <- regardeInstruction
  case instruction of
    GA -> do nb <- regardeReservoirPompeCourante
             if nb == PasPoubelle GA
               then vaFinBoucle
               else ajouteBoucle
    BU -> vaDebutBoucle >> retireBoucle
    ZO -> inverseSens
    MEU -> annuleMode
  when (instruction /= BU) (avanceUnCoup)

parsage :: String -> [Mot] -> [Mot]
parsage [] acc = acc
parsage ('G':'A':xs) acc = parsage xs (acc ++ [GA])
parsage ('B':'U':xs) acc = parsage xs (acc ++ [BU])
parsage ('Z':'O':xs) acc = parsage xs (acc ++ [ZO])
parsage ('M':'E':'U':xs) acc = parsage xs (acc ++ [MEU])
parsage (_:xs) acc = parsage xs acc

faitBoulot :: String -> IO ()
faitBoulot fichier = do
  doesFileExist fichier >>= erreurGuard "Avec un fichier existant, ca serait plus facile..."
  getPermissions fichier >>= return . readable >>= erreurGuard "Avec un fichier lisible, ca serait plus facile..."
  contenu <- readFile fichier
  let mots' = parsage (map toUpper contenu) []
  erreurGuard ("Pas de GA, de BU, de ZO ou de MEU dans " ++ fichier) (not $ null mots')
  hSetBuffering stdin NoBuffering
  evalStateT interprete $ creeShadoko mots'

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> erreur "Pas de nom de fichier a interpreter ?"
            (fichier:_) -> do faitBoulot fichier
                              exitWith ExitSuccess
