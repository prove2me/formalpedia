-- Prove2me | solution 1 for BianchiIX.stableRescaledHessian_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T15:16:37.607876+00:00
-- url     : https://prove2.me/submissions/0a43cff2-a95d-47d0-b69e-5e939693ebab

import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Theorems.Thm_BianchiIX_stableBoundaryHessian_mixed_bound
import Theorems.Thm_BianchiIX_stableBoundaryJacobian_wall_bound
import Theorems.Thm_BianchiIX_stableRescaledJacobian_center_bounds
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

private theorem BianchiIX.stableOriginalField_norm_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    ‖stableOriginalField y‖ ≤ 6 * (|y 1| + |y 2|) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  change |(6 / stableBoundaryDenom y) * stableBoundaryField y i| ≤ _
  rw [show (6 / stableBoundaryDenom y) * stableBoundaryField y i =
    6 * (stableBoundaryField y i / stableBoundaryDenom y) by ring, abs_mul]
  norm_num only
  exact mul_le_mul_of_nonneg_left (stableBoundaryField_div_component hc hm hu hw i) (by norm_num)

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

private theorem BianchiIX.stableRescaledJacobian_apply_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    ‖(c + 1) • (stableOriginalJacobian y).mulVec v‖ ≤
      64 * (|y 1| + |y 2|) * ‖v‖ + 36 * (c + 1) * ‖![v 1, v 2]‖ := by
  have hK : 0 < c + 1 := by linarith
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hb1 : |y 1| + |y 2| ≤ 1 := by linarith
  have h0 (i : Fin 3) : |(c + 1) * stableOriginalJacobian y i 0| ≤ 64 * (|y 1| + |y 2|) := by
    have H := stableRescaledJacobian_center_bounds hc hm hu hw
    have H' := stableRescaledJacobian_center_column hc hm hu hw
    fin_cases i
    · exact H.1.trans (by nlinarith)
    · exact H'.1.trans (by linarith [abs_nonneg (y 2)])
    · exact H'.2.trans (by linarith [abs_nonneg (y 1)])
  have hz (i j : Fin 3) (hj : j ≠ 0) :
      |(c + 1) * stableOriginalJacobian y i j| ≤ 18 * (c + 1) := by
    rw [abs_mul, abs_of_pos hK]
    nlinarith only [mul_le_mul_of_nonneg_left (stableOriginalJacobian_wall_bound hc hm hu hw i j hj) hK.le]
  have hv0 : |v 0| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
  have hv1 : |v 1| ≤ ‖![v 1, v 2]‖ := by simpa only [Real.norm_eq_abs, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 0
  have hv2 : |v 2| ≤ ‖![v 1, v 2]‖ := by simpa only [Real.norm_eq_abs, Matrix.cons_val_one, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 1
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have heq : ((c + 1) • (stableOriginalJacobian y).mulVec v) i =
      ((c + 1) * stableOriginalJacobian y i 0) * v 0 +
        ((c + 1) * stableOriginalJacobian y i 1) * v 1 +
        ((c + 1) * stableOriginalJacobian y i 2) * v 2 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  rw [heq, Real.norm_eq_abs]
  have H := (abs_add_le (((c + 1) * stableOriginalJacobian y i 0) * v 0 +
    ((c + 1) * stableOriginalJacobian y i 1) * v 1) (((c + 1) * stableOriginalJacobian y i 2) * v 2)).trans
      (add_le_add (abs_add_le _ _) (le_refl _))
  have H0 := mul_le_mul (h0 i) hv0 (abs_nonneg _) (by positivity)
  have H1 := mul_le_mul (hz i 1 (by decide)) hv1 (abs_nonneg _) (by positivity)
  have H2 := mul_le_mul (hz i 2 (by decide)) hv2 (abs_nonneg _) (by positivity)
  simp only [abs_mul] at H H0 H1 H2
  nlinarith only [H, H0, H1, H2]

private theorem BianchiIX.stableHessian_clock_term_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    ‖(dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) •
        ((c + 1) • (stableOriginalJacobian y).mulVec w)‖ ≤
      384 * (|y 1| + |y 2|) * ‖v‖ * ‖w‖ + 648 * ‖v‖ * ‖![w 1, w 2]‖ := by
  have hD := stableBoundaryDenom_pos y
  have hK : 0 < c + 1 := by linarith
  have hs1 : (c + 1) / stableBoundaryDenom y ≤ 1 :=
    (div_le_one hD).mpr (stableBoundaryDenom_lower hc hm).2
  have hs2 : (c + 1) ^ 2 / stableBoundaryDenom y ≤ 3 :=
    (div_le_iff₀ hD).mpr (by nlinarith [(stableBoundaryDenom_lower hc hm).1])
  have hratio : |dotProduct (stableDenomGradient y) v / stableBoundaryDenom y| ≤
      (6 * (c + 1) / stableBoundaryDenom y) * ‖v‖ := by
    rw [abs_div, abs_of_pos hD]
    have H := div_le_div_of_nonneg_right (stableDenomGradient_bound hc hm hu hw v) hD.le
    convert! H using 1
    ring
  rw [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ ((6 * (c + 1) / stableBoundaryDenom y) * ‖v‖) *
        (64 * (|y 1| + |y 2|) * ‖w‖ + 36 * (c + 1) * ‖![w 1, w 2]‖) :=
      mul_le_mul hratio (stableRescaledJacobian_apply_bound hc hm hu hw w) (norm_nonneg _) (by positivity)
    _ = ((c + 1) / stableBoundaryDenom y) * (384 * (|y 1| + |y 2|) * ‖v‖ * ‖w‖) +
        ((c + 1) ^ 2 / stableBoundaryDenom y) * (216 * ‖v‖ * ‖![w 1, w 2]‖) := by ring
    _ ≤ 1 * (384 * (|y 1| + |y 2|) * ‖v‖ * ‖w‖) + 3 * (216 * ‖v‖ * ‖![w 1, w 2]‖) :=
      add_le_add (mul_le_mul_of_nonneg_right hs1 (by positivity))
        (mul_le_mul_of_nonneg_right hs2 (by positivity))
    _ = _ := by ring

theorem solution {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    ‖(c + 1) • stableOriginalHessian y v w‖ ≤ 1024 * stableHessianBudget y v w := by
  let K := c + 1
  let D := stableBoundaryDenom y
  let b := |y 1| + |y 2|
  let R := b * ‖v‖ * ‖w‖
  let S := ‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖
  let T0 := (6 * K / D) • stableBoundaryHessian y v w
  let T1 := (dotProduct (stableDenomGradient y) v / D) • (K • (stableOriginalJacobian y).mulVec w)
  let T2 := (dotProduct (stableDenomGradient y) w / D) • (K • (stableOriginalJacobian y).mulVec v)
  let T3 := (stableDenomHessian v w / D) • (K • stableOriginalField y)
  have hD : 0 < D := stableBoundaryDenom_pos y
  have hK : 0 < K := by dsimp [K]; linarith
  have hs1 : K / D ≤ 1 := (div_le_one hD).mpr (stableBoundaryDenom_lower hc hm).2
  have hs2 : K ^ 2 / D ≤ 3 := (div_le_iff₀ hD).mpr (by nlinarith [(stableBoundaryDenom_lower hc hm).1])
  have hR : 0 ≤ R := by dsimp [R, b]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT0 : ‖T0‖ ≤ 6 * R + 216 * S := by
    dsimp only [T0]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 6 * K / D)]
    have H := mul_le_mul_of_nonneg_left (stableBoundaryHessian_mixed_bound hc hm hu hw v w)
      (show 0 ≤ 6 * K / D by positivity)
    calc
      _ ≤ (6 * K / D) * (R + 12 * K * S) := H
      _ = (K / D) * (6 * R) + (K ^ 2 / D) * (72 * S) := by ring
      _ ≤ 1 * (6 * R) + 3 * (72 * S) :=
        add_le_add (mul_le_mul_of_nonneg_right hs1 (by positivity))
          (mul_le_mul_of_nonneg_right hs2 (by positivity))
      _ = _ := by ring
  have hT1 := stableHessian_clock_term_bound hc hm hu hw v w
  have hT2 := stableHessian_clock_term_bound hc hm hu hw w v
  have hT3 : ‖T3‖ ≤ 60 * R := by
    dsimp only [T3]
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hK,
      abs_div, abs_of_pos hD]
    have H := mul_le_mul (stableDenomHessian_bound v w) (stableOriginalField_norm_bound hc hm hu hw)
      (norm_nonneg _) (by positivity)
    calc
      _ = (K / D) * (|stableDenomHessian v w| * ‖stableOriginalField y‖) := by ring
      _ ≤ 1 * ((10 * ‖v‖ * ‖w‖) * (6 * b)) :=
        mul_le_mul hs1 H (by positivity) (by norm_num)
      _ = 60 * R := by dsimp [R]; ring
  have heq : K • stableOriginalHessian y v w = T0 - T1 - T2 - T3 := by
    rw [stableOriginalHessian_factor]
    ext i
    dsimp [T0, T1, T2, T3, K, D]
    ring
  have H1 := norm_sub_le T0 T1
  have H2 := norm_sub_le (T0 - T1) T2
  have H3 := norm_sub_le (T0 - T1 - T2) T3
  change ‖K • stableOriginalHessian y v w‖ ≤ _
  rw [heq]
  change ‖T1‖ ≤ _ at hT1
  change ‖T2‖ ≤ _ at hT2
  dsimp [stableHessianBudget, R, S, b] at hT0 hT3 hR hS ⊢
  nlinarith only [H1, H2, H3, hT0, hT1, hT2, hT3, hR, hS]
