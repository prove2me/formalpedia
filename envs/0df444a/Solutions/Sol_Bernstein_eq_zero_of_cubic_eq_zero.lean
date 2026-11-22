-- Prove2me | solution 1 for Bernstein.eq_zero_of_cubic_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T17:36:32.283812+00:00
-- url     : https://prove2.me/submissions/2c41cfd9-283e-4f2c-9603-87c2794ba068

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein.Arith

open WeierstrassCurve

theorem cubic_part1 (p : ℕ) [Fact p.Prime] (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) :
    ∀ x : ZMod p, x ^ 3 + (A : ZMod p) * x ^ 2 + x = 0 → x = 0 := by
  intro x hx
  by_contra h0
  apply hA
  refine ⟨x - x⁻¹, ?_⟩
  have hq : x ^ 2 + (A : ZMod p) * x + 1 = 0 := by
    have : x * (x ^ 2 + (A : ZMod p) * x + 1) = 0 := by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left h0
  have hinv : x⁻¹ = -(x + (A : ZMod p)) := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination -hq
  rw [hinv]
  linear_combination (-4 : ZMod p) * hq

theorem eq_zero_of_cubic_eq_zero_dev (p : ℕ) [Fact p.Prime] (_hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) :
    (∀ x : ZMod p, x ^ 3 + (A : ZMod p) * x ^ 2 + x = 0 → x = 0) ∧
    (∀ x : ZMod p, x ≠ 0 → ¬ (Ecurve p A).Equation (emb p x) 0) := by
  refine ⟨cubic_part1 p A hA, ?_⟩
  intro x hx heq
  apply hx
  apply cubic_part1 p A hA
  rw [Affine.equation_iff] at heq
  simp [Ecurve, curve, WeierstrassCurve.baseChange, WeierstrassCurve.map] at heq
  apply (emb p).injective
  simp only [map_add, map_mul, map_pow, map_intCast, map_zero]
  linear_combination -heq

end Bernstein.Arith

theorem solution : type_of% @Bernstein.Arith.eq_zero_of_cubic_eq_zero_dev := @Bernstein.Arith.eq_zero_of_cubic_eq_zero_dev
