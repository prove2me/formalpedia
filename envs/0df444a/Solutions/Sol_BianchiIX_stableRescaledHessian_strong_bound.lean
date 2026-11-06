-- Prove2me | solution 1 for BianchiIX.stableRescaledHessian_strong_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:25:09.045839+00:00
-- url     : https://prove2.me/submissions/4f3a3f54-f206-4a55-881e-37f2d50bc363

import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Theorems.Thm_BianchiIX_stableBoundaryJacobian_wall_bound
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

private theorem BianchiIX.stable_boundary_field (m u w : ℝ) :
    phaseVelocity m u 0 w = m * u ^ 2 - (m + 1) * u * w + w ^ 2 ∧
    strongVelocity m u 0 w = stableStrongRate m u w * u ∧
    activeVelocity m u 0 w = 0 ∧
    weakVelocity m u 0 w = stableWeakRate m u w * w := by
  unfold phaseVelocity strongVelocity activeVelocity weakVelocity coupling
    stableStrongRate stableWeakRate
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · ring

end
end

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

private theorem BianchiIX.stable_boundary_phase_bound {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10) :
    |phaseVelocity m u 0 w / (c + 1)| ≤
      u ^ 2 + 2 * |u| * |w| + w ^ 2 / (c + 1) := by
  obtain ⟨hK, _, hm0, hmK, hm1, hm1K⟩ := stable_boundary_band hc hm
  have hK0 : 0 < c + 1 := by linarith
  rw [(stable_boundary_field m u w).1, abs_div, abs_of_pos hK0]
  apply (div_le_iff₀ hK0).mpr
  have H := (abs_add_le (m * u ^ 2 - (m + 1) * u * w) (w ^ 2)).trans
    (add_le_add (abs_sub _ _) le_rfl)
  rw [abs_mul, abs_of_nonneg hm0, abs_of_nonneg (sq_nonneg u),
    abs_mul, abs_mul, abs_of_nonneg hm1, abs_of_nonneg (sq_nonneg w)] at H
  have hU := mul_le_mul_of_nonneg_right hmK (sq_nonneg u)
  have hUW := mul_le_mul_of_nonneg_right hm1K (mul_nonneg (abs_nonneg u) (abs_nonneg w))
  have heq : (u ^ 2 + 2 * |u| * |w| + w ^ 2 / (c + 1)) * (c + 1) =
      (c + 1) * u ^ 2 + 2 * (c + 1) * (|u| * |w|) + w ^ 2 := by
    field_simp
  rw [heq]
  nlinarith only [H, hU, hUW]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_pos (y : StableState) : 0 < stableBoundaryDenom y := by
  unfold stableBoundaryDenom
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomGradient_dotProduct (y v : StableState) :
    dotProduct (stableDenomGradient y) v =
      2 * y 0 * v 0 + 2 * (y 1 - y 2) * (v 1 - v 2) := by
  simp [stableDenomGradient, dotProduct, Fin.sum_univ_succ]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalJacobian_mulVec (y v : StableState) :
    (stableOriginalJacobian y).mulVec v =
      (6 / stableBoundaryDenom y) • (stableBoundaryJacobian y).mulVec v -
        (6 * dotProduct (stableDenomGradient y) v / stableBoundaryDenom y ^ 2) •
          stableBoundaryField y := by
  ext i
  simp [stableOriginalJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

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

private theorem BianchiIX.stableBoundary_field_div_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableBoundaryField y 1 / stableBoundaryDenom y| ≤ |y 1| ∧
      |stableBoundaryField y 2 / stableBoundaryDenom y| ≤ |y 2| := by
  have H := stableBoundary_rate_denom_bounds hc hm hu hw
  have hD := stableBoundaryDenom_pos y
  constructor
  · rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    change |stableStrongRate (y 0) (y 1) (y 2) * y 1| ≤ _
    rw [abs_mul, mul_comm _ (stableBoundaryDenom y)]
    exact mul_le_mul_of_nonneg_right H.1 (abs_nonneg _)
  · rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    change |stableWeakRate (y 0) (y 1) (y 2) * y 2| ≤ _
    rw [abs_mul, mul_comm _ (stableBoundaryDenom y)]
    exact mul_le_mul_of_nonneg_right H.2 (abs_nonneg _)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalJacobian_factor (y : StableState) (i j : Fin 3) :
    stableOriginalJacobian y i j = 6 / stableBoundaryDenom y *
      (stableBoundaryJacobian y i j - stableBoundaryField y i / stableBoundaryDenom y *
        stableDenomGradient y j) := by
  unfold stableOriginalJacobian
  field_simp [(stableBoundaryDenom_pos y).ne']

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

private theorem BianchiIX.stableBoundary_phase_div_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    |stableBoundaryField y 0 / stableBoundaryDenom y| ≤ (|y 1| + |y 2|) ^ 2 := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have H := stable_boundary_phase_bound (u := y 1) (w := y 2) hc hm
  have hw : y 2 ^ 2 / (c + 1) ≤ y 2 ^ 2 :=
    div_le_self (sq_nonneg _) (by linarith)
  have H' : |stableBoundaryField y 0 / (c + 1)| ≤ (|y 1| + |y 2|) ^ 2 := by
    rw [(stable_boundary_field (y 0) (y 1) (y 2)).1] at H
    change |stableBoundaryField y 0 / (c + 1)| ≤ _ at H
    nlinarith [sq_abs (y 1), sq_abs (y 2)]
  rw [abs_div, abs_of_pos hK] at H'
  have H'' := (div_le_iff₀ hK).mp H'
  rw [abs_div, abs_of_pos hD]
  apply (div_le_iff₀ hD).mpr
  exact H''.trans (mul_le_mul_of_nonneg_left (stableBoundaryDenom_lower hc hm).2 (sq_nonneg _))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_scaled_entry_bound {y : StableState} {c B : ℝ} {i j : Fin 3}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) (hB : 0 ≤ B)
    (hentry : |stableBoundaryJacobian y i j -
      stableBoundaryField y i / stableBoundaryDenom y * stableDenomGradient y j| ≤ 3 * (c + 1) * B) :
    |(c + 1) * stableOriginalJacobian y i j| ≤ 64 * B := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hscale : 6 * (c + 1) ^ 2 / stableBoundaryDenom y ≤ 18 := by
    apply (div_le_iff₀ hD).mpr
    nlinarith [(stableBoundaryDenom_lower hc hm).1]
  rw [stableOriginalJacobian_factor, abs_mul, abs_of_pos hK, abs_mul,
    abs_of_pos (by positivity : 0 < 6 / stableBoundaryDenom y)]
  calc
    _ ≤ (c + 1) * (6 / stableBoundaryDenom y * (3 * (c + 1) * B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hentry (by positivity)) hK.le
    _ = (6 * (c + 1) ^ 2 / stableBoundaryDenom y) * (3 * B) := by ring
    _ ≤ 18 * (3 * B) := mul_le_mul_of_nonneg_right hscale (by positivity)
    _ ≤ 64 * B := by linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledJacobian_center_column {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |(c + 1) * stableOriginalJacobian y 1 0| ≤ 64 * |y 1| ∧
    |(c + 1) * stableOriginalJacobian y 2 0| ≤ 64 * |y 2| := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have H := stableBoundary_field_div_bounds hc hm hu hw
  have hg : |stableDenomGradient y 0| ≤ 2 * (c + 1) := by
    change |2 * y 0| ≤ _
    rw [abs_of_nonneg (by positivity)]
    linarith
  constructor
  · apply stable_scaled_entry_bound hc hm (abs_nonneg _)
    have hf : |stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 0| ≤
        2 * (c + 1) * |y 1| := by
      rw [abs_mul]
      nlinarith [mul_le_mul H.1 hg (abs_nonneg _) (abs_nonneg _)]
    have hp : |stableBoundaryJacobian y 1 0| ≤ (c + 1) * |y 1| := by
      change |-y 0 * y 1| ≤ _
      rw [abs_mul, abs_neg, abs_of_nonneg hm0]
      exact mul_le_mul_of_nonneg_right hmK (abs_nonneg _)
    have H' := abs_sub (stableBoundaryJacobian y 1 0)
      (stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 0)
    linarith
  · apply stable_scaled_entry_bound hc hm (abs_nonneg _)
    have hf : |stableBoundaryField y 2 / stableBoundaryDenom y * stableDenomGradient y 0| ≤
        2 * (c + 1) * |y 2| := by
      rw [abs_mul]
      nlinarith [mul_le_mul H.2 hg (abs_nonneg _) (abs_nonneg _)]
    have hp : |stableBoundaryJacobian y 2 0| ≤ (c + 1) * |y 2| := by
      change |-y 2| ≤ _
      rw [abs_neg]
      nlinarith [abs_nonneg (y 2)]
    have H' := abs_sub (stableBoundaryJacobian y 2 0)
      (stableBoundaryField y 2 / stableBoundaryDenom y * stableDenomGradient y 0)
    linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledJacobian_strong_weak {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |(c + 1) * stableOriginalJacobian y 1 2| ≤ 18 * |y 1| * (|y 1| + |y 2|) := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hscale : (c + 1) * (6 / stableBoundaryDenom y) ≤ 6 := by
    have H := (stableBoundaryDenom_lower hc hm).2
    rw [show (c + 1) * (6 / stableBoundaryDenom y) =
      (6 * (c + 1)) / stableBoundaryDenom y by ring]
    apply (div_le_iff₀ hD).mpr
    linarith
  have hg : |stableDenomGradient y 2| ≤ 2 * (|y 1| + |y 2|) := by
    change |2 * (y 2 - y 1)| ≤ _
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have H := abs_sub (y 2) (y 1)
    linarith
  have hf := (stableBoundary_field_div_bounds hc hm hu hw).1
  have hprod : |stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 2| ≤
      2 * |y 1| * (|y 1| + |y 2|) := by
    rw [abs_mul]
    nlinarith only [mul_le_mul hf hg (abs_nonneg _) (abs_nonneg _)]
  have hp : |stableBoundaryJacobian y 1 2| ≤ |y 1| * (|y 1| + |y 2|) := by
    change |-y 1 * y 2| ≤ _
    rw [abs_mul, abs_neg]
    nlinarith [sq_nonneg |y 1|]
  have hb : |stableBoundaryJacobian y 1 2 -
      stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 2| ≤
        3 * |y 1| * (|y 1| + |y 2|) := by
    have H := abs_sub (stableBoundaryJacobian y 1 2)
      (stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 2)
    linarith
  rw [stableOriginalJacobian_factor, abs_mul, abs_of_pos hK, abs_mul,
    abs_of_pos (by positivity : 0 < 6 / stableBoundaryDenom y), ← mul_assoc]
  have H := mul_le_mul hscale hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
  nlinarith only [H]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalHessian_factor (y v w : StableState) :
    stableOriginalHessian y v w =
      (6 / stableBoundaryDenom y) • stableBoundaryHessian y v w -
        (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) •
          (stableOriginalJacobian y).mulVec w -
        (dotProduct (stableDenomGradient y) w / stableBoundaryDenom y) •
          (stableOriginalJacobian y).mulVec v -
        (stableDenomHessian v w / stableBoundaryDenom y) • stableOriginalField y := by
  simp only [stableOriginalJacobian_mulVec]
  ext i
  dsimp [stableOriginalHessian, stableOriginalField]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryField_div_component {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (i : Fin 3) :
    |stableBoundaryField y i / stableBoundaryDenom y| ≤ |y 1| + |y 2| := by
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hb1 : |y 1| + |y 2| ≤ 1 := by linarith
  have H := stableBoundary_field_div_bounds hc hm hu hw
  fin_cases i
  · exact (stableBoundary_phase_div_bound hc hm).trans (by nlinarith)
  · exact H.1.trans (by linarith [abs_nonneg (y 2)])
  · exact H.2.trans (by linarith [abs_nonneg (y 1)])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomGradient_wall_bound (y : StableState) (j : Fin 3) (hj : j ≠ 0) :
    |stableDenomGradient y j| ≤ 2 * (|y 1| + |y 2|) := by
  fin_cases j
  · exact (hj rfl).elim
  · change |2 * (y 1 - y 2)| ≤ _
    rw [abs_mul]
    norm_num only
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
  · change |2 * (y 2 - y 1)| ≤ _
    rw [abs_mul]
    norm_num only
    have H := abs_sub (y 2) (y 1)
    linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomGradient_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    |dotProduct (stableDenomGradient y) v| ≤ 6 * (c + 1) * ‖v‖ := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have hg (j : Fin 3) : |stableDenomGradient y j| ≤ 2 * (c + 1) := by
    by_cases hj : j = 0
    · subst j
      change |2 * y 0| ≤ _
      rw [abs_of_nonneg (by positivity)]
      linarith
    · exact (stableDenomGradient_wall_bound y j hj).trans (by linarith)
  have hv (j : Fin 3) : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
  have hprod (j : Fin 3) : |stableDenomGradient y j * v j| ≤ 2 * (c + 1) * ‖v‖ := by
    rw [abs_mul]
    exact mul_le_mul (hg j) (hv j) (abs_nonneg _) (by positivity)
  calc
    _ ≤ ∑ j, |stableDenomGradient y j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, 2 * (c + 1) * ‖v‖ := Finset.sum_le_sum (fun j _ => hprod j)
    _ = _ := by simp; ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomHessian_bound (v w : StableState) :
    |stableDenomHessian v w| ≤ 10 * ‖v‖ * ‖w‖ := by
  have hv (j : Fin 3) : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
  have hw (j : Fin 3) : |w j| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w j
  have hvd : |v 1 - v 2| ≤ 2 * ‖v‖ := (abs_sub _ _).trans (by linarith [hv 1, hv 2])
  have hwd : |w 1 - w 2| ≤ 2 * ‖w‖ := (abs_sub _ _).trans (by linarith [hw 1, hw 2])
  have H0 := mul_le_mul (hv 0) (hw 0) (abs_nonneg _) (norm_nonneg _)
  have H1 := mul_le_mul hvd hwd (abs_nonneg _) (by positivity)
  have H := abs_add_le (2 * v 0 * w 0) (2 * (v 1 - v 2) * (w 1 - w 2))
  simp only [abs_mul] at H
  norm_num only at H
  change |stableDenomHessian v w| ≤ _ at H
  nlinarith only [H, H0, H1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalJacobian_wall_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (i j : Fin 3) (hj : j ≠ 0) :
    |stableOriginalJacobian y i j| ≤ 18 := by
  have hD := stableBoundaryDenom_pos y
  have hD3 : 3 ≤ stableBoundaryDenom y := by
    unfold stableBoundaryDenom
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1 - y 2)]
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hb1 : |y 1| + |y 2| ≤ 1 := by linarith
  have hprod : |stableBoundaryField y i / stableBoundaryDenom y * stableDenomGradient y j| ≤ 2 := by
    rw [abs_mul]
    have H := mul_le_mul (stableBoundaryField_div_component hc hm hu hw i)
      (stableDenomGradient_wall_bound y j hj) (abs_nonneg _) hb
    nlinarith
  have H := abs_sub (stableBoundaryJacobian y i j)
    (stableBoundaryField y i / stableBoundaryDenom y * stableDenomGradient y j)
  have hbracket : |stableBoundaryJacobian y i j -
      stableBoundaryField y i / stableBoundaryDenom y * stableDenomGradient y j| ≤
      3 * stableBoundaryDenom y := by
    linarith [stableBoundaryJacobian_wall_bound hc hm hu hw i j hj]
  rw [stableOriginalJacobian_factor, abs_mul, abs_of_pos (by positivity : 0 < 6 / stableBoundaryDenom y)]
  calc
    _ ≤ (6 / stableBoundaryDenom y) * (3 * stableBoundaryDenom y) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = 18 := by field_simp; norm_num

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomGradient_split_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) (v : StableState) :
    |dotProduct (stableDenomGradient y) v| ≤
      2 * (c + 1) * |v 0| + 4 * (|y 1| + |y 2|) * ‖v‖ := by
  obtain ⟨_, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have hdiff : |v 1 - v 2| ≤ 2 * ‖v‖ := by
    have h1 := norm_le_pi_norm v 1
    have h2 := norm_le_pi_norm v 2
    simp only [Real.norm_eq_abs] at h1 h2
    exact (abs_sub _ _).trans (by linarith)
  have H0 := mul_le_mul_of_nonneg_right (show |y 0| ≤ c + 1 by rwa [abs_of_nonneg hm0]) (abs_nonneg (v 0))
  have H1 := mul_le_mul (abs_sub (y 1) (y 2)) hdiff (abs_nonneg _) (by positivity)
  rw [stableDenomGradient_dotProduct]
  have H := abs_add_le (2 * y 0 * v 0) (2 * (y 1 - y 2) * (v 1 - v 2))
  simp only [abs_mul] at H
  norm_num only at H
  nlinarith only [H, H0, H1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryHessian_strong_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) (v w : StableState) :
    |stableBoundaryHessian y v w 1| ≤
      5 * |y 1| * ‖v‖ * ‖w‖ + (c + 1) * (|v 0| * |w 1| + |v 1| * |w 0|) +
        (|y 1| + |y 2|) * (|v 1| * ‖w‖ + ‖v‖ * |w 1|) := by
  obtain ⟨_, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have hv (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hw (i : Fin 3) : |w i| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w i
  have hp (i : Fin 3) := mul_le_mul (hv i) (hw i) (abs_nonneg _) (norm_nonneg _)
  have hT : |v 0 * w 1 + v 1 * w 0| ≤ |v 0| * |w 1| + |v 1| * |w 0| := by
    simpa only [abs_mul] using abs_add_le (v 0 * w 1) (v 1 * w 0)
  have hS : |v 1 * w 2 + v 2 * w 1| ≤ |v 1| * ‖w‖ + ‖v‖ * |w 1| := by
    have H := abs_add_le (v 1 * w 2) (v 2 * w 1)
    simp only [abs_mul] at H
    nlinarith only [H, mul_le_mul_of_nonneg_left (hw 2) (abs_nonneg (v 1)),
      mul_le_mul_of_nonneg_right (hv 2) (abs_nonneg (w 1))]
  have hM := mul_le_mul (show |y 0| ≤ c + 1 by rwa [abs_of_nonneg hm0]) hT (abs_nonneg _) (by linarith)
  have hW := mul_le_mul (show |y 2| ≤ |y 1| + |y 2| by linarith [abs_nonneg (y 1)])
    hS (abs_nonneg _) (by positivity)
  have H0 := mul_le_mul_of_nonneg_left (hp 0) (abs_nonneg (y 1))
  have H1 := mul_le_mul_of_nonneg_left (hp 1) (abs_nonneg (y 1))
  have H2 := mul_le_mul_of_nonneg_left (hp 2) (abs_nonneg (y 1))
  have Ha := abs_sub (-y 1 * v 0 * w 0) (y 0 * (v 0 * w 1 + v 1 * w 0))
  have Hb := abs_add_le (-y 1 * v 0 * w 0 - y 0 * (v 0 * w 1 + v 1 * w 0)) (3 * y 1 * v 1 * w 1)
  have Hc := abs_sub (-y 1 * v 0 * w 0 - y 0 * (v 0 * w 1 + v 1 * w 0) + 3 * y 1 * v 1 * w 1)
    (y 2 * (v 1 * w 2 + v 2 * w 1))
  have Hd := abs_sub (-y 1 * v 0 * w 0 - y 0 * (v 0 * w 1 + v 1 * w 0) + 3 * y 1 * v 1 * w 1 -
    y 2 * (v 1 * w 2 + v 2 * w 1)) (y 1 * v 2 * w 2)
  change |stableBoundaryHessian y v w 1| ≤ _ at Hd
  simp only [abs_mul, abs_neg] at Ha Hb Hc Hd
  norm_num only at Ha Hb Hc Hd
  nlinarith only [Ha, Hb, Hc, Hd, H0, H1, H2, hM, hW]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalField_strong_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableOriginalField y 1| ≤ 6 * |y 1| := by
  have H := mul_le_mul_of_nonneg_left (stableBoundary_field_div_bounds hc hm hu hw).1
    (by norm_num : (0 : ℝ) ≤ 6)
  change |(6 / stableBoundaryDenom y) * stableBoundaryField y 1| ≤ _
  rw [show (6 / stableBoundaryDenom y) * stableBoundaryField y 1 =
    6 * (stableBoundaryField y 1 / stableBoundaryDenom y) by ring, abs_mul]
  norm_num only
  exact H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledJacobian_strong_offDiagonal {y v : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |(c + 1) * stableOriginalJacobian y 1 0 * v 0 +
      (c + 1) * stableOriginalJacobian y 1 2 * v 2| ≤ 96 * |y 1| * ‖v‖ := by
  have h0 := (stableRescaledJacobian_center_column hc hm hu hw).1
  have h2 : |(c + 1) * stableOriginalJacobian y 1 2| ≤ 18 * |y 1| :=
    (stableRescaledJacobian_strong_weak hc hm hu hw).trans
      (mul_le_of_le_one_right (by positivity) (by linarith : |y 1| + |y 2| ≤ 1))
  have hv (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have H0 := mul_le_mul h0 (hv 0) (abs_nonneg _) (by positivity)
  have H2 := mul_le_mul h2 (hv 2) (abs_nonneg _) (by positivity)
  have H := abs_add_le ((c + 1) * stableOriginalJacobian y 1 0 * v 0)
    ((c + 1) * stableOriginalJacobian y 1 2 * v 2)
  simp only [abs_mul] at H H0 H2
  nlinarith only [H, H0, H2, mul_nonneg (abs_nonneg (y 1)) (norm_nonneg v)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledJacobian_strong_apply {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    |(c + 1) * (stableOriginalJacobian y).mulVec v 1| ≤
      96 * |y 1| * ‖v‖ + 18 * (c + 1) * |v 1| := by
  have hK : 0 < c + 1 := by linarith
  have hd : |(c + 1) * stableOriginalJacobian y 1 1 * v 1| ≤ 18 * (c + 1) * |v 1| := by
    rw [abs_mul, abs_mul, abs_of_pos hK]
    have H := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (stableOriginalJacobian_wall_bound hc hm hu hw 1 1 (by decide)) hK.le)
      (abs_nonneg (v 1))
    nlinarith only [H]
  have heq : (c + 1) * (stableOriginalJacobian y).mulVec v 1 =
      ((c + 1) * stableOriginalJacobian y 1 0 * v 0 + (c + 1) * stableOriginalJacobian y 1 2 * v 2) +
        (c + 1) * stableOriginalJacobian y 1 1 * v 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (stableRescaledJacobian_strong_offDiagonal hc hm hu hw) hd)

end
end

private theorem BianchiIX.stableStrongHessian_clock_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    |(dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) *
        ((c + 1) * (stableOriginalJacobian y).mulVec w 1)| ≤
      576 * |y 1| * ‖v‖ * ‖w‖ + 108 * |v 0| * |w 1| +
        72 * (|y 1| + |y 2|) * ‖v‖ * |w 1| := by
  let K := c + 1
  let D := stableBoundaryDenom y
  let b := |y 1| + |y 2|
  let d := |dotProduct (stableDenomGradient y) v| / D
  have hD : 0 < D := stableBoundaryDenom_pos y
  have hK : 0 < K := by dsimp [K]; linarith
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hs1 : K / D ≤ 1 := (div_le_one hD).mpr (stableBoundaryDenom_lower hc hm).2
  have hs2 : K ^ 2 / D ≤ 3 := (div_le_iff₀ hD).mpr (by nlinarith [(stableBoundaryDenom_lower hc hm).1])
  have hratio : d ≤ (6 * K / D) * ‖v‖ := by
    convert! div_le_div_of_nonneg_right (stableDenomGradient_bound hc hm hu hw v) hD.le using 1
    ring
  have hsplit : d ≤ (2 * K / D) * |v 0| + (4 * b / D) * ‖v‖ := by
    convert! div_le_div_of_nonneg_right (stableDenomGradient_split_bound hc hm v) hD.le using 1
    ring
  have hleft : d * (96 * |y 1| * ‖w‖) ≤ 576 * |y 1| * ‖v‖ * ‖w‖ := by
    calc
      _ ≤ ((6 * K / D) * ‖v‖) * (96 * |y 1| * ‖w‖) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = (K / D) * (576 * |y 1| * ‖v‖ * ‖w‖) := by ring
      _ ≤ 1 * (576 * |y 1| * ‖v‖ * ‖w‖) := mul_le_mul_of_nonneg_right hs1 (by positivity)
      _ = _ := one_mul _
  have hright : d * (18 * K * |w 1|) ≤ 108 * |v 0| * |w 1| + 72 * b * ‖v‖ * |w 1| := by
    calc
      _ ≤ ((2 * K / D) * |v 0| + (4 * b / D) * ‖v‖) * (18 * K * |w 1|) :=
        mul_le_mul_of_nonneg_right hsplit (by positivity)
      _ = (K ^ 2 / D) * (36 * |v 0| * |w 1|) + (K / D) * (72 * b * ‖v‖ * |w 1|) := by ring
      _ ≤ 3 * (36 * |v 0| * |w 1|) + 1 * (72 * b * ‖v‖ * |w 1|) :=
        add_le_add (mul_le_mul_of_nonneg_right hs2 (by positivity))
          (mul_le_mul_of_nonneg_right hs1 (by dsimp [b]; positivity))
      _ = _ := by ring
  rw [abs_mul, abs_div, abs_of_pos hD]
  have H := mul_le_mul_of_nonneg_left (stableRescaledJacobian_strong_apply hc hm hu hw w) hd
  change d * |(c + 1) * (stableOriginalJacobian y).mulVec w 1| ≤ _
  dsimp only [K, b] at hright H
  nlinarith only [H, hleft, hright]

theorem solution {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    |((c + 1) • stableOriginalHessian y v w) 1| ≤ 2048 * stableStrongHessianBudget y v w := by
  let K := c + 1
  let D := stableBoundaryDenom y
  let R := |y 1| * ‖v‖ * ‖w‖
  let T := |v 0| * |w 1| + |v 1| * |w 0|
  let S := (|y 1| + |y 2|) * (|v 1| * ‖w‖ + ‖v‖ * |w 1|)
  let T0 := (6 * K / D) * stableBoundaryHessian y v w 1
  let T1 := (dotProduct (stableDenomGradient y) v / D) * (K * (stableOriginalJacobian y).mulVec w 1)
  let T2 := (dotProduct (stableDenomGradient y) w / D) * (K * (stableOriginalJacobian y).mulVec v 1)
  let T3 := (stableDenomHessian v w / D) * (K * stableOriginalField y 1)
  have hD : 0 < D := stableBoundaryDenom_pos y
  have hK : 0 < K := by dsimp [K]; linarith
  have hs1 : K / D ≤ 1 := (div_le_one hD).mpr (stableBoundaryDenom_lower hc hm).2
  have hs2 : K ^ 2 / D ≤ 3 := (div_le_iff₀ hD).mpr (by nlinarith [(stableBoundaryDenom_lower hc hm).1])
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT0 : |T0| ≤ 30 * R + 18 * T + 6 * S := by
    dsimp only [T0]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 6 * K / D)]
    calc
      _ ≤ (6 * K / D) * (5 * R + K * T + S) := by
        have H := mul_le_mul_of_nonneg_left (stableBoundaryHessian_strong_bound hc hm v w)
          (show 0 ≤ 6 * K / D by positivity)
        convert! H using 1
        dsimp [R, K, T, S]
        ring
      _ = (K / D) * (30 * R + 6 * S) + (K ^ 2 / D) * (6 * T) := by ring
      _ ≤ 1 * (30 * R + 6 * S) + 3 * (6 * T) :=
        add_le_add (mul_le_mul_of_nonneg_right hs1 (by positivity))
          (mul_le_mul_of_nonneg_right hs2 (by positivity))
      _ = _ := by ring
  have hT1 := stableStrongHessian_clock_bound hc hm hu hw v w
  have hT2 := stableStrongHessian_clock_bound hc hm hu hw w v
  have hT3 : |T3| ≤ 60 * R := by
    dsimp only [T3]
    rw [abs_mul, abs_div, abs_mul, abs_of_pos hD, abs_of_pos hK]
    have H := mul_le_mul (stableDenomHessian_bound v w) (stableOriginalField_strong_bound hc hm hu hw)
      (abs_nonneg _) (by positivity)
    calc
      _ = (K / D) * (|stableDenomHessian v w| * |stableOriginalField y 1|) := by ring
      _ ≤ 1 * ((10 * ‖v‖ * ‖w‖) * (6 * |y 1|)) :=
        mul_le_mul hs1 H (by positivity) (by norm_num)
      _ = _ := by dsimp [R]; ring
  have heq : ((c + 1) • stableOriginalHessian y v w) 1 = T0 - T1 - T2 - T3 := by
    rw [stableOriginalHessian_factor]
    dsimp [T0, T1, T2, T3, K, D]
    ring
  rw [heq]
  have H1 := abs_sub T0 T1
  have H2 := abs_sub (T0 - T1) T2
  have H3 := abs_sub (T0 - T1 - T2) T3
  change |T1| ≤ _ at hT1
  change |T2| ≤ _ at hT2
  dsimp [stableStrongHessianBudget, R, T, S] at hT0 hT3 hR hT hS ⊢
  nlinarith only [H1, H2, H3, hT0, hT1, hT2, hT3, hR, hT, hS]
