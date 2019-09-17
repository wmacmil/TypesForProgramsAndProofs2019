module ThierryLecture1 where

--confused about what to import
open import Agda.Builtin.Equality

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

data Nat : Set where
  Z : Nat
  S : Nat → Nat

_+_ : Nat → Nat → Nat
x + Z = x
x + S y = S (x + y)

max : Nat → Nat → Nat
max Z Z = Z
max Z (S y) = S y
max (S x) Z = S x
max (S x) (S y) = S (max x y)

two = S (S Z)
three = S (S (S Z))

data Exp : Set where
  Const : Nat → Exp
  Add : Exp → Exp → Exp

val : Exp → Nat
val (Const x) = x
val (Add e e₁) = (val e) + (val e₁)

depth : Exp → Nat
depth (Const x) = Z
depth (Add e e₁) = S (max (depth e) (depth e₁))

data _⟶_ : Exp → Exp → Set where
  C-rule : (n₀ n₁ : Nat) → (Add (Const n₀) (Const n₁)) ⟶ Const (n₀ + n₁)
  A₀ : (e₀ e₁ e₂ : Exp) → (e₀ ⟶ e₁) → ((Add e₀ e₂) ⟶ (Add e₁ e₂))
  A₁ : (n : Nat) → (e₀ e₁ : Exp) → (e₀ ⟶ e₁) → (Add (Const n) e₀ ⟶ Add (Const n) e₁)

data _⟶*_ : Exp → Exp → Set where
  id-rule : (e₀ e₁ : Exp) → e₀ ≡ e₁ → e₀ ⟶* e₁
  carry : (e₀ e₁ e₂ : Exp) → (e₀ ⟶ e₁) → (e₁ ⟶* e₂) → (e₀ ⟶* e₂)

data star : (Exp → Exp → Set) → (Exp → Exp → Set) where
  star-id : (e₀ e₁ : Exp) → (R : Exp → Exp → Set ) → e₀ ≡ e₁ → star R e₀ e₁
  star-trans : (e₀ e₁ e₂ : Exp) → (R : Exp → Exp → Set ) → R e₀ e₁ → R e₁ e₂ → star R e₀ e₂

reflexive : (Exp → Exp → Set) → Set
reflexive R = (e : Exp) → R e e

transitive : (Exp → Exp → Set) → Set
transitive R = (e₀ e₁ e₂ : Exp) →  R e₀ e₁ → R e₁ e₂ → R e₀ e₂

-- claim : star is reflexive and trans

reflexivity-of-star : (R : Exp → Exp → Set) → reflexive (star R)
reflexivity-of-star R r = star-id r r R refl

transitivity-of-star : (R : Exp → Exp → Set) → transitive (star R)
transitivity-of-star R e0 e1 e2 (star-id .e0 .e1 .R x) s2 = {!!}
transitivity-of-star R e0 e1 e2 (star-trans .e0 e₁ .e1 .R x x₁) s2 = {!!}

deterministic : (Exp → Exp → Set) → Set
deterministic R = (e e₀ e₁ : Exp) → R e e₀ → R e e₁ → e₀ ≡ e₁

-- claim, ⟶ is deterministic


