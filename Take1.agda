module Take1 where

open import Agda.Primitive

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-Elim : ∀ (P : ℕ → Set) → P 0 → (∀ (n : ℕ) → P n → P (suc n)) → ∀ (n : ℕ) → P n
ℕ-Elim P pz ih zero = pz
ℕ-Elim P pz ih (suc n) = ih n (ℕ-Elim P pz ih n)

-- natural number addition

_+_ : ℕ → ℕ → ℕ
zero + m  = m
suc n + m = suc (n + m)

-- addition using induction over natural numbers.

_`+_ : ℕ → ℕ → ℕ
n `+ m = ℕ-Elim (λ _ → ℕ) m (λ _ ac → suc ac) n

module Equality where

  infix 4 _≡_

  data _≡_ {l}{A : Set l}(x : A) : A → Set l where
    refl : x ≡ x

  {-# BUILTIN EQUALITY _≡_ #-}
  {-# BUILTIN REFL refl #-}

  -- some useful properties of equality

  sym : ∀ {l}{A : Set l}{x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  trans : ∀ {l}{A : Set l}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  cong : ∀ {l}{A B : Set l}{x y : A}(f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  -- equality proof combinators

  infixr 1 _≡⟨_⟩_ _∎

  _≡⟨_⟩_ : ∀ {l}{A : Set l}(x : A) {y z} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ xy ⟩ yz = trans xy yz

  _∎ : ∀ {l}{A : Set l}(x : A) → x ≡ x
  x ∎ = refl

open Equality

--simple equality proofs

test1 : 2 + 2 ≡ 4
test1 = refl

-- definitions of addition are equivalent

lemma : ∀ (n m : ℕ) → (suc n) `+ m ≡ suc (n `+ m)
lemma zero m = refl
lemma (suc n) m = refl

equivalent : ∀ (n m : ℕ) → n + m ≡ n `+ m
equivalent zero m = refl
equivalent (suc n) m = sym (trans (lemma n m) (cong suc (sym (equivalent n m))))

equivalent' : ∀ (n m : ℕ) → n + m ≡ n `+ m
equivalent' zero m = refl
equivalent' (suc n) m = suc (n + m)   ≡⟨ cong suc (equivalent' n m) ⟩
                         suc (n `+ m) ≡⟨ cong suc refl ⟩
                         suc n `+ m
                        ∎

-- commutativity of addition

+-zeror : ∀ (n : ℕ) → n + 0 ≡ n
+-zeror zero = refl
+-zeror (suc n) = cong suc (+-zeror n)

+-suc : ∀ (n m : ℕ) → suc (n + m) ≡ n + suc m
+-suc zero m = refl
+-suc (suc n) m = cong suc (+-suc n m)

+-comm : forall (n m : ℕ) → n + m ≡ m + n
+-comm zero m = sym (+-zeror m)
+-comm (suc n) m = suc (n + m) ≡⟨ cong suc (+-comm n m) ⟩
                   suc (m + n) ≡⟨ +-suc m n ⟩
                   m + suc n
                 ∎
