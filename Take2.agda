module Take2 where

open import Agda.Primitive
open import Take1

-- list data type

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

-- list head function, maybe version

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

headList : ∀ {A : Set} → List A → Maybe A
headList [] = nothing
headList (x ∷ _) = just x

-- vector data type

data Vec {l}(A : Set l) : ℕ → Set l where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)


-- head function

head : ∀ {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ _) = x


module Product where

  infixr 4 _,_

  record Σ {l l'}(A : Set l)(B : A → Set l') : Set (l ⊔ l') where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ

  _×_ : ∀ (A B : Set) → Set
  A × B = Σ A (λ _ → B)

open Product

-- zip definitions

zipList : ∀ {A B} → List A → List B → List (A × B)
zipList [] ys = []
zipList (x ∷ xs) [] = []
zipList (x ∷ xs) (y ∷ ys) = (x , y) ∷ zipList xs ys

zip : ∀ {A B n} → Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

-- finite set

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)


finElim : ∀ (P : (n : ℕ) → Fin n → Set) → (∀ {n} → P (suc n) (zero {n})) → (∀ n (i : Fin n) → P n i → P (suc n) (suc i)) → ∀ n i → P n i
finElim P Base IH (suc n) zero = Base
finElim P Base IH (suc n) (suc n') = IH n n' (finElim P Base IH n n')


-- lookup

lookupList : ∀ {A} → ℕ → List A → Maybe A
lookupList _ [] = nothing
lookupList zero (x ∷ _) = just x
lookupList (suc n) (_ ∷ xs) = lookupList n xs

lookup : ∀ {A : Set}{n} → Fin n → Vec A n → A
lookup zero (x ∷ xs) = x
lookup (suc n') (_ ∷ xs) = lookup n' xs
