-- Prove2me | solution 1 for BianchiIX.shearTail_constraint_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:04:01.232725+00:00
-- url     : https://prove2.me/submissions/35290928-5d3b-4562-abbe-1f0e79016bf4

import Definitions.Def_BianchiIX_Algebra_Flow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.curvature_abs_le_sum_sq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |curvature a b c| ≤ (a + b + c) ^ 2 := by
  rw [abs_le]
  constructor
  · unfold curvature
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  · unfold curvature
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]

end
end

/-- The small growing-wall tail has a quadratic projection denominator. -/
theorem solution {a p s n x y : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hp : p < 0)
    (hs : a / 2 ≤ s ∧ s ≤ 3 * a)
    (hn : 0 ≤ n ∧ n ≤ a ^ 2) (hx : 0 ≤ x ∧ x ≤ a ^ 2)
    (hy : 0 ≤ y ∧ y ≤ a / 16) (hc : constraint p s n x y = 1) :
    |curvature n x y| ≤ a ^ 2 / 128 ∧
      a ^ 2 / 5 ≤ 1 - p ^ 2 ∧ 1 - p ^ 2 ≤ 10 * a ^ 2 ∧
      -1 < p ∧ p ≤ -(15 / 16) ∧
      a ^ 2 / 10 ≤ 1 + p ∧ 1 + p ≤ 6 * a ^ 2 := by
  have ha2 : a ^ 2 ≤ a / 256 := by nlinarith only [ha.1, ha.2]
  have hsum : n + x + y ≤ 9 * a / 128 := by linarith only [hn.2, hx.2, hy.2, ha2]
  have hsum2 := pow_le_pow_left₀ (by positivity [hn.1, hx.1, hy.1] : 0 ≤ n + x + y) hsum 2
  have hQ : |curvature n x y| ≤ a ^ 2 / 128 :=
    (curvature_abs_le_sum_sq hn.1 hx.1 hy.1).trans (by nlinarith only [hsum2, sq_nonneg a])
  have hs0 : 0 ≤ s := by linarith only [hs.1, ha.1]
  have hslo := pow_le_pow_left₀ (div_nonneg ha.1.le (by norm_num) : 0 ≤ a / 2) hs.1 2
  have hshi := pow_le_pow_left₀ hs0 hs.2 2
  have HC : p ^ 2 + s ^ 2 + curvature n x y = 1 := hc
  have hlo : a ^ 2 / 5 ≤ 1 - p ^ 2 := by nlinarith only [HC, hslo, (abs_le.mp hQ).1, sq_nonneg a]
  have hhi : 1 - p ^ 2 ≤ 10 * a ^ 2 := by nlinarith only [HC, hshi, (abs_le.mp hQ).2, sq_nonneg a]
  have hplo : -1 < p := by nlinarith only [hlo, ha.1, hp]
  have hphi : p ≤ -(15 / 16) := by
    have haSq := pow_le_pow_left₀ ha.1.le ha.2 2
    nlinarith only [hhi, haSq, hp, sq_nonneg (p + 15 / 16)]
  refine ⟨hQ, hlo, hhi, hplo, hphi, ?_, ?_⟩
  · nlinarith only [hlo, sq_nonneg (1 + p)]
  · have H := mul_le_mul_of_nonneg_right (show (5 : ℝ) / 3 ≤ 1 - p by linarith only [hphi])
      (show 0 ≤ 1 + p by linarith only [hplo])
    nlinarith only [H, hhi]
