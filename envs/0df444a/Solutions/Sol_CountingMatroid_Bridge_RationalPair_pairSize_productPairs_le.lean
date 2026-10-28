-- Prove2me | solution 1 for CountingMatroid.Bridge.RationalPair.pairSize_productPairs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T22:09:13.076802+00:00
-- url     : https://prove2.me/submissions/e3e68154-a878-43bf-8af5-d57802f385a5

import Definitions.Def_CountingMatroidBridgeRationalPairProducts

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

/-- Componentwise rational-pair multiplication adds the operand widths. -/
theorem pairSize_mul_tight (x y : Pair) :
    pairSize (mul x y) ≤ pairSize x + pairSize y := by
  have h₁ : Nat.size (x.1 * y.1) ≤ Nat.size x.1 + Nat.size y.1 :=
    size_mul_le x.1 y.1
  have h₂ : Nat.size (x.2 * y.2) ≤ Nat.size x.2 + Nat.size y.2 :=
    size_mul_le x.2 y.2
  dsimp [pairSize, mul]
  omega

/-- A product of m pairs, each of width at most S, has width at most
2 + m*S. Thus repeated multiplication does not cause exponential width growth
in the unreduced representation. -/
theorem solution (xs : List Pair) (S : ℕ)
    (hS : ∀ x ∈ xs, pairSize x ≤ S) :
    pairSize (productPairs xs) ≤ 2 + xs.length * S := by
  induction xs with
  | nil => simp [productPairs, pairSize]
  | cons x xs ih =>
      have hx : pairSize x ≤ S := hS x (by simp)
      have htail := ih (by
        intro y hy
        exact hS y (by simp [hy]))
      calc
        pairSize (productPairs (x :: xs))
            ≤ pairSize x + pairSize (productPairs xs) := by
                simp only [productPairs]
                exact pairSize_mul_tight x (productPairs xs)
        _ ≤ S + (2 + xs.length * S) := Nat.add_le_add hx htail
        _ = 2 + (xs.length + 1) * S := by
          rw [Nat.add_mul, Nat.one_mul]
          omega


