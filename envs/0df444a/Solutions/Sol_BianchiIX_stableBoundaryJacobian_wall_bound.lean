-- Prove2me | solution 1 for BianchiIX.stableBoundaryJacobian_wall_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T15:10:50.371443+00:00
-- url     : https://prove2.me/submissions/bb312349-aeb4-4fef-8495-96b8d64ecaab

import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_band {m c : ℝ} (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10) :
    3 ≤ c + 1 ∧ 5 / 8 * (c + 1) ≤ m ∧ 0 ≤ m ∧ m ≤ c + 1 ∧
      0 ≤ m + 1 ∧ m + 1 ≤ 2 * (c + 1) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hm
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_rates {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10)
    (hu : |u| ≤ 1 / 100) (hw : |w| ≤ 1 / 100) :
    stableStrongRate m u w / (c + 1) ≤ -(c + 1) / 8 ∧
      stableWeakRate m u w / (c + 1) ≤ -(1 / 4) := by
  obtain ⟨hK, hml, hm0, _, _, _⟩ := stable_boundary_band hc hm
  have hK0 : 0 < c + 1 := by linarith
  have hu2 : u ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := sq_le_sq.mpr (by norm_num; exact hu)
  have huw : |u * w| ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hw (abs_nonneg _) (by norm_num)
  have hm2 := (sq_le_sq₀ (by positivity : 0 ≤ (5 / 8 : ℝ) * (c + 1)) hm0).mpr hml
  constructor
  · apply (div_le_iff₀ hK0).mpr
    unfold stableStrongRate
    nlinarith [sq_nonneg w, sq_nonneg (c + 1 - 3)]
  · apply (div_le_iff₀ hK0).mpr
    unfold stableWeakRate
    nlinarith [(abs_le.mp huw).1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundary_rate_denom_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableStrongRate (y 0) (y 1) (y 2)| ≤ stableBoundaryDenom y ∧
      |stableWeakRate (y 0) (y 1) (y 2)| ≤ stableBoundaryDenom y := by
  have hK : 0 < c + 1 := by linarith
  have hr := stable_boundary_rates hc hm hu hw
  have hs := (div_le_iff₀ hK).mp hr.1
  have hw' := (div_le_iff₀ hK).mp hr.2
  have hs0 : stableStrongRate (y 0) (y 1) (y 2) ≤ 0 := by nlinarith
  have hw0 : stableWeakRate (y 0) (y 1) (y 2) ≤ 0 := by nlinarith
  rw [abs_of_nonpos hs0, abs_of_nonpos hw0]
  have huw : |y 1 * y 2| ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hw (abs_nonneg _) (by norm_num)
  obtain ⟨huwl, huwu⟩ := abs_le.mp huw
  unfold stableStrongRate stableWeakRate stableBoundaryDenom
  constructor
  · nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2)]
  · nlinarith [sq_nonneg (y 0 - 1 / 2), sq_nonneg (y 1), sq_nonneg (y 2)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_lower {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    (c + 1) ^ 2 ≤ 3 * stableBoundaryDenom y ∧ c + 1 ≤ stableBoundaryDenom y := by
  obtain ⟨hK, hml, hm0, _, _, _⟩ := stable_boundary_band hc hm
  have hm2 := (sq_le_sq₀ (by positivity : 0 ≤ (5 / 8 : ℝ) * (c + 1)) hm0).mpr hml
  unfold stableBoundaryDenom
  constructor
  · nlinarith [sq_nonneg (y 1 - y 2)]
  · nlinarith [sq_nonneg (y 1 - y 2), sq_nonneg (c + 1 - 3)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundary_polynomial_center_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    |stableBoundaryJacobian y 0 0| ≤ (|y 1| + |y 2|) ^ 2 ∧
    |stableBoundaryJacobian y 0 1| ≤ 2 * (c + 1) * (|y 1| + |y 2|) ∧
    |stableBoundaryJacobian y 0 2| ≤ 2 * (c + 1) * (|y 1| + |y 2|) := by
  obtain ⟨hK, _, hm0, hmK, hm1, hm1K⟩ := stable_boundary_band hc hm
  constructor
  · change |y 1 ^ 2 - y 1 * y 2| ≤ _
    have H := abs_sub (y 1 ^ 2) (y 1 * y 2)
    rw [abs_of_nonneg (sq_nonneg (y 1)), abs_mul] at H
    nlinarith [sq_abs (y 1), sq_abs (y 2), mul_nonneg (abs_nonneg (y 1)) (abs_nonneg (y 2))]
  constructor
  · change |2 * y 0 * y 1 - (y 0 + 1) * y 2| ≤ _
    have H := abs_sub (2 * y 0 * y 1) ((y 0 + 1) * y 2)
    simp only [abs_mul, abs_of_nonneg hm0, abs_of_nonneg hm1,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    nlinarith [mul_le_mul_of_nonneg_right hmK (abs_nonneg (y 1)),
      mul_le_mul_of_nonneg_right hm1K (abs_nonneg (y 2))]
  · change |-(y 0 + 1) * y 1 + 2 * y 2| ≤ _
    have H := abs_add_le (-(y 0 + 1) * y 1) (2 * y 2)
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hm1, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    nlinarith [mul_le_mul_of_nonneg_right hm1K (abs_nonneg (y 1)),
      mul_nonneg (by linarith : 0 ≤ c) (abs_nonneg (y 2))]

end
end

theorem solution {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (i j : Fin 3) (hj : j ≠ 0) :
    |stableBoundaryJacobian y i j| ≤ 2 * stableBoundaryDenom y := by
  have hD3 : 3 ≤ stableBoundaryDenom y := by
    unfold stableBoundaryDenom
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1 - y 2)]
  have hKD := (stableBoundaryDenom_lower hc hm).2
  have hK : 0 ≤ c + 1 := by linarith
  have hb : |y 1| + |y 2| ≤ 1 := by linarith
  have hu2 : y 1 ^ 2 ≤ 1 := by nlinarith [sq_abs (y 1), abs_nonneg (y 1)]
  have hw2 : y 2 ^ 2 ≤ 1 := by nlinarith [sq_abs (y 2), abs_nonneg (y 2)]
  have huw : |y 1 * y 2| ≤ 1 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hu hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 100)]
  have hcenter := stableBoundary_polynomial_center_bounds hc hm
  have hcenter' : 2 * (c + 1) * (|y 1| + |y 2|) ≤ 2 * stableBoundaryDenom y := by
    nlinarith [mul_le_of_le_one_right (show 0 ≤ 2 * (c + 1) by positivity) hb]
  have hrate := stableBoundary_rate_denom_bounds hc hm hu hw
  fin_cases i <;> fin_cases j
  · exact (hj rfl).elim
  · exact hcenter.2.1.trans hcenter'
  · exact hcenter.2.2.trans hcenter'
  · exact (hj rfl).elim
  · change |(1 - y 0 ^ 2 - y 2 ^ 2 + 3 * y 1 ^ 2) / 2| ≤ _
    have heq : (1 - y 0 ^ 2 - y 2 ^ 2 + 3 * y 1 ^ 2) / 2 =
        stableStrongRate (y 0) (y 1) (y 2) + y 1 ^ 2 := by
      unfold stableStrongRate; ring
    rw [heq]
    have H := abs_add_le (stableStrongRate (y 0) (y 1) (y 2)) (y 1 ^ 2)
    rw [abs_of_nonneg (sq_nonneg (y 1))] at H
    linarith
  · change |-y 1 * y 2| ≤ _
    rw [neg_mul, abs_neg]
    linarith
  · exact (hj rfl).elim
  · change |(2 * y 1 - y 2) * y 2| ≤ _
    have heq : (2 * y 1 - y 2) * y 2 = 2 * (y 1 * y 2) - y 2 ^ 2 := by ring
    rw [heq]
    have H := abs_sub (2 * (y 1 * y 2)) (y 2 ^ 2)
    rw [abs_mul, abs_of_nonneg (sq_nonneg (y 2))] at H
    norm_num only at H
    linarith
  · change |-(y 0 + 1 + 2 * y 1 * y 2 - y 1 ^ 2)| ≤ _
    have heq : -(y 0 + 1 + 2 * y 1 * y 2 - y 1 ^ 2) =
        stableWeakRate (y 0) (y 1) (y 2) - y 1 * y 2 := by
      unfold stableWeakRate; ring
    rw [heq]
    have H := abs_sub (stableWeakRate (y 0) (y 1) (y 2)) (y 1 * y 2)
    linarith
