-- Prove2me | solution 1 for BianchiIX.normalizedState_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:29:03.280165+00:00
-- url     : https://prove2.me/submissions/5010ba72-7f6f-4cf5-b498-2fac5eb13942

import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open BianchiIX
open Set MeasureTheory

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

theorem solution {x : NormalizedState} {M : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (hwall : ∀ i : Fin 3, wallValue i x ≤ M) : ‖x‖ ≤ 1 + 3 * M := by
  have hM : 0 ≤ M := (le_of_lt hpos.1).trans (hwall 0)
  have hQ := (abs_le.mp (curvature_abs_le_sum_sq hpos.1.le hpos.2.1.le hpos.2.2.le)).1
  have hsum : x 2 + x 3 + x 4 ≤ 3 * M := by
    have h₁ := hwall 0
    have h₂ := hwall 1
    have h₃ := hwall 2
    change x 2 ≤ M at h₁
    change x 3 ≤ M at h₂
    change x 4 ≤ M at h₃
    linarith
  have hsum2 := pow_le_pow_left₀ (by linarith [hpos.1, hpos.2.1, hpos.2.2] : 0 ≤ x 2 + x 3 + x 4) hsum 2
  have hconstraint : x 0 ^ 2 + x 1 ^ 2 + curvature (x 2) (x 3) (x 4) = 1 := hcon
  have hS : x 0 ^ 2 + x 1 ^ 2 ≤ 1 + 9 * M ^ 2 := by nlinarith
  have hR : 0 ≤ 1 + 3 * M := by positivity
  have h₀ : |x 0| ≤ 1 + 3 * M := by
    apply (sq_le_sq₀ (abs_nonneg _) hR).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (x 1)]
  have h₁ : |x 1| ≤ 1 + 3 * M := by
    apply (sq_le_sq₀ (abs_nonneg _) hR).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (x 0)]
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i
  · exact h₀
  · exact h₁
  · have H := hwall 0
    change x 2 ≤ M at H
    change |x 2| ≤ 1 + 3 * M
    rw [abs_of_pos hpos.1]
    linarith
  · have H := hwall 1
    change x 3 ≤ M at H
    change |x 3| ≤ 1 + 3 * M
    rw [abs_of_pos hpos.2.1]
    linarith
  · have H := hwall 2
    change x 4 ≤ M at H
    change |x 4| ≤ 1 + 3 * M
    rw [abs_of_pos hpos.2.2]
    linarith
