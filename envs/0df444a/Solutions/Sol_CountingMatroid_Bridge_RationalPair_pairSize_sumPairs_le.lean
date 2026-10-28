-- Prove2me | solution 1 for CountingMatroid.Bridge.RationalPair.pairSize_sumPairs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T22:01:22.520574+00:00
-- url     : https://prove2.me/submissions/bbdeb0e7-7172-4326-849e-849bb2f935a5

import Definitions.Def_CountingMatroidBridgeRationalPairSums

set_option autoImplicit false

open CountingMatroid.Bridge.RationalPair

/-- Binary width of a product is at most the sum of the operand widths. -/
theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.2
  by_cases hb : b = 0
  · simp [hb]
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    have h₁ := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) hbpos
    have h₂ := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b)
      (by positivity : 0 < 2 ^ Nat.size a)
    rw [pow_add]
    exact h₁.trans h₂

/-- Binary width of a sum is at most the larger operand width plus one. -/
theorem size_add_le (a b : ℕ) : Nat.size (a + b) ≤ max (Nat.size a) (Nat.size b) + 1 := by
  apply Nat.size_le.2
  let m := max (Nat.size a) (Nat.size b)
  have ha : a < 2 ^ m := by
    exact lt_of_lt_of_le (Nat.lt_size_self a)
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have hb : b < 2 ^ m := by
    exact lt_of_lt_of_le (Nat.lt_size_self b)
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  calc
    a + b < 2 ^ m + 2 ^ m := Nat.add_lt_add ha hb
    _ = 2 ^ (m + 1) := by rw [pow_succ]; omega

/-- Addition's output width is at most twice the combined input width, plus
one carry bit. -/
theorem pairSize_add_le (x y : Pair) :
    pairSize (add x y) ≤ 2 * (pairSize x + pairSize y) + 1 := by
  have h₁ : Nat.size (x.1 * y.2) ≤ pairSize x + pairSize y := by
    have h := size_mul_le x.1 y.2
    dsimp [pairSize] at *
    omega
  have h₂ : Nat.size (y.1 * x.2) ≤ pairSize x + pairSize y := by
    have h := size_mul_le y.1 x.2
    dsimp [pairSize] at *
    omega
  have h₃ : Nat.size (x.2 * y.2) ≤ pairSize x + pairSize y := by
    have h := size_mul_le x.2 y.2
    dsimp [pairSize] at *
    omega
  have hnum : Nat.size (x.1 * y.2 + y.1 * x.2) ≤ pairSize x + pairSize y + 1 := by
    calc
      Nat.size (x.1 * y.2 + y.1 * x.2) ≤
          max (Nat.size (x.1 * y.2)) (Nat.size (y.1 * x.2)) + 1 := size_add_le ..
      _ ≤ pairSize x + pairSize y + 1 := by omega
  calc
    pairSize (add x y) =
        Nat.size (x.1 * y.2 + y.1 * x.2) + Nat.size (x.2 * y.2) := by
          simp [pairSize, add]
    _ ≤ (pairSize x + pairSize y + 1) + (pairSize x + pairSize y) :=
      Nat.add_le_add hnum h₃
    _ = 2 * (pairSize x + pairSize y) + 1 := by omega

/-- Multiplication and division-by-a-positive-pair each have output width at
most twice the total input width. -/
theorem pairSize_mul_le (x y : Pair) :
    pairSize (mul x y) ≤ 2 * (pairSize x + pairSize y) := by
  have h₁ : Nat.size (x.1 * y.1) ≤ pairSize x + pairSize y := by
    have h := size_mul_le x.1 y.1
    dsimp [pairSize] at *
    omega
  have h₂ : Nat.size (x.2 * y.2) ≤ pairSize x + pairSize y := by
    have h := size_mul_le x.2 y.2
    dsimp [pairSize] at *
    omega
  calc
    pairSize (mul x y) = Nat.size (x.1 * y.1) + Nat.size (x.2 * y.2) := by
      simp [pairSize, mul]
    _ ≤ (pairSize x + pairSize y) + (pairSize x + pairSize y) := Nat.add_le_add h₁ h₂
    _ = 2 * (pairSize x + pairSize y) := by omega

theorem pairSize_div_le (x y : Pair) :
    pairSize (div x y) ≤ 2 * (pairSize x + pairSize y) := by
  have h₁ : Nat.size (x.1 * y.2) ≤ pairSize x + pairSize y := by
    have h := size_mul_le x.1 y.2
    dsimp [pairSize] at *
    omega
  have h₂ : Nat.size (x.2 * y.1) ≤ pairSize x + pairSize y := by
    have h := size_mul_le x.2 y.1
    dsimp [pairSize] at *
    omega
  calc
    pairSize (div x y) = Nat.size (x.1 * y.2) + Nat.size (x.2 * y.1) := by
      simp [pairSize, div]
    _ ≤ (pairSize x + pairSize y) + (pairSize x + pairSize y) := Nat.add_le_add h₁ h₂
    _ = 2 * (pairSize x + pairSize y) := by omega

/-- The numerator width after addition is controlled by the two cross-products. -/
theorem numeratorSize_add_le (x y : Pair) :
    Nat.size (add x y).1 ≤
      max (Nat.size x.1 + Nat.size y.2) (Nat.size y.1 + Nat.size x.2) + 1 := by
  simp only [add]
  calc
    Nat.size (x.1 * y.2 + y.1 * x.2) ≤
        max (Nat.size (x.1 * y.2)) (Nat.size (y.1 * x.2)) + 1 := size_add_le ..
    _ ≤ max (Nat.size x.1 + Nat.size y.2) (Nat.size y.1 + Nat.size x.2) + 1 := by
      have h₁ := size_mul_le x.1 y.2
      have h₂ := size_mul_le y.1 x.2
      exact Nat.add_le_add_right (max_le_max h₁ h₂) 1

/-- The denominator width after addition is at most the sum of denominator widths. -/
theorem denominatorSize_add_le (x y : Pair) :
    Nat.size (add x y).2 ≤ Nat.size x.2 + Nat.size y.2 := by
  simp only [add]
  exact size_mul_le x.2 y.2

/-- A left-associated sum of individually bounded rational pairs has polynomial
representation width: each new addend increases the largest component width by
at most its width plus one. -/
theorem maxComponentSize_sumPairs_le (xs : List Pair) (S : ℕ)
    (hS : ∀ x ∈ xs, pairSize x ≤ S) :
    max (Nat.size (sumPairs xs).1) (Nat.size (sumPairs xs).2) ≤
      1 + xs.length * (S + 1) := by
  induction xs with
  | nil => simp [sumPairs]
  | cons x xs ih =>
      have hx : pairSize x ≤ S := hS x (by simp)
      have htail := ih (by
        intro y hy
        exact hS y (by simp [hy]))
      have hxa : Nat.size x.1 ≤ S := by
        dsimp [pairSize] at hx
        omega
      have hxb : Nat.size x.2 ≤ S := by
        dsimp [pairSize] at hx
        omega
      have hta : Nat.size (sumPairs xs).1 ≤ 1 + xs.length * (S + 1) :=
        (le_max_left _ _).trans htail
      have htb : Nat.size (sumPairs xs).2 ≤ 1 + xs.length * (S + 1) :=
        (le_max_right _ _).trans htail
      have hnum := numeratorSize_add_le x (sumPairs xs)
      have hden := denominatorSize_add_le x (sumPairs xs)
      have hcross : max (Nat.size x.1 + Nat.size (sumPairs xs).2)
          (Nat.size (sumPairs xs).1 + Nat.size x.2) ≤
          S + (1 + xs.length * (S + 1)) := by
        apply max_le_iff.mpr
        constructor <;> omega
      change max (Nat.size (add x (sumPairs xs)).1)
        (Nat.size (add x (sumPairs xs)).2) ≤ _
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      apply max_le_iff.mpr
      constructor
      · calc
          Nat.size (add x (sumPairs xs)).1 ≤
              max (Nat.size x.1 + Nat.size (sumPairs xs).2)
                (Nat.size (sumPairs xs).1 + Nat.size x.2) + 1 := hnum
          _ ≤ S + (1 + xs.length * (S + 1)) + 1 := Nat.add_le_add_right hcross 1
          _ = 1 + (xs.length * (S + 1) + (S + 1)) := by ring
      · calc
          Nat.size (add x (sumPairs xs)).2 ≤ Nat.size x.2 + Nat.size (sumPairs xs).2 := hden
          _ ≤ S + (1 + xs.length * (S + 1)) := Nat.add_le_add hxb htb
          _ ≤ 1 + (xs.length * (S + 1) + (S + 1)) := by
            calc
              S + (1 + xs.length * (S + 1)) ≤
                  (S + 1) + (1 + xs.length * (S + 1)) :=
                Nat.add_le_add_right (Nat.le_succ S) _
              _ = 1 + (xs.length * (S + 1) + (S + 1)) := by ring

theorem solution (xs : List Pair) (S : ℕ)
    (hS : ∀ x ∈ xs, pairSize x ≤ S) :
    pairSize (sumPairs xs) ≤ 2 * (1 + xs.length * (S + 1)) := by
  have h := maxComponentSize_sumPairs_le xs S hS
  unfold pairSize
  have h₁ := le_max_left (Nat.size (sumPairs xs).1) (Nat.size (sumPairs xs).2)
  have h₂ := le_max_right (Nat.size (sumPairs xs).1) (Nat.size (sumPairs xs).2)
  omega


