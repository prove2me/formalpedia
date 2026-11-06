-- Prove2me | solution 1 for BianchiIX.exists_stableBoundaryProjection_refined_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:53:17.628827+00:00
-- url     : https://prove2.me/submissions/67abee3e-4a94-4151-a89f-8fd298d49f74

import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_exists_stableCorrectedRemainder_amplitude_bounds
import Theorems.Thm_BianchiIX_stableCorrectedPhase_directional_bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Arsinh
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
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open BianchiIX
open Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_stableCorrectedPhase (n : WithTop ℕ∞) {y : Fin 3 → ℝ}
    (hm : 1 < y 0) :
    ContDiffAt ℝ n (fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2)) y := by
  have hL : y 0 + 1 ≠ 0 := by linarith
  have hD : y 0 ^ 2 - 1 ≠ 0 := by nlinarith
  have hS : (y 0 + 1) ^ 2 + y 2 ^ 2 ≠ 0 := by
    have h : 0 < y 0 + 1 := by linarith
    positivity
  unfold stableCorrectedPhase stableWeakRadius phaseNorm stableCorrectionA stableCorrectionC
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableBoundaryProjection_two {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContDiffAt ℝ 2 (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y :=
  contDiffAt_stableBoundaryProjection_two_in_band hm (by simp) hu hw

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

attribute [local instance] BianchiIX.instNormedAddCommGroupContinuousLinearMapRealIdStableState_1
attribute [local instance] BianchiIX.instNormedSpaceRealContinuousLinearMapIdStableState_1
private theorem BianchiIX.stableBoundaryProjection_derivative_decomposition {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
    let Q := fun z : StableState => stableCorrectedPhase (z 0) (z 1) (z 2)
    fderiv ℝ P y = fderiv ℝ stableCorrectedRemainder y + fderiv ℝ Q y ∧
      fderiv ℝ (fderiv ℝ P) y = fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y + fderiv ℝ (fderiv ℝ Q) y := by
  let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  let Q := fun z : StableState => stableCorrectedPhase (z 0) (z 1) (z 2)
  have hP : ContDiffAt ℝ 2 P y := contDiffAt_stableBoundaryProjection_two hm hu hw
  have hQ : ContDiffAt ℝ 2 Q y := contDiffAt_stableCorrectedPhase 2 (by linarith)
  have hfirst : fderiv ℝ stableCorrectedRemainder y = fderiv ℝ P y - fderiv ℝ Q y :=
    fderiv_fun_sub (hP.differentiableAt (by norm_num)) (hQ.differentiableAt (by norm_num))
  have heq : fderiv ℝ stableCorrectedRemainder =ᶠ[𝓝 y] (fun z => fderiv ℝ P z - fderiv ℝ Q z) := by
    filter_upwards [hP.eventually (by norm_num), hQ.eventually (by norm_num)] with z hp hq
    exact fderiv_fun_sub (hp.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num))
  have hsecond : fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y =
      fderiv ℝ (fderiv ℝ P) y - fderiv ℝ (fderiv ℝ Q) y := by
    rw [heq.fderiv_eq]
    exact fderiv_fun_sub
      ((hP.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num))
      ((hQ.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num))
  exact ⟨(sub_eq_iff_eq_add).mp hfirst.symm, (sub_eq_iff_eq_add).mp hsecond.symm⟩

end
end

attribute [local instance] BianchiIX.instNormedAddCommGroupContinuousLinearMapRealIdStableState_1
attribute [local instance] BianchiIX.instNormedSpaceRealContinuousLinearMapIdStableState_1

theorem solution :
    ∃ C > (0 : ℝ), ∀ y : StableState, 2 ≤ y 0 → |y 1| < 1 / 200 → |y 2| < 1 / 200 →
      let b := |y 1| + |y 2|
      let L := y 0 + 1
      let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
      (∀ v, v 1 = 0 → v 2 = 0 → |fderiv ℝ P y v - v 0| ≤ C / L ^ 2 * b ^ 2 * ‖v‖) ∧
      (∀ v, v 0 = 0 → |fderiv ℝ P y v| ≤ C / L * b * ‖v‖) ∧
      (∀ v r, v 1 = 0 → v 2 = 0 → r 1 = 0 → r 2 = 0 →
        |fderiv ℝ (fderiv ℝ P) y v r| ≤ C / L ^ 3 * b ^ 2 * ‖v‖ * ‖r‖) ∧
      (∀ v r, v 1 = 0 → v 2 = 0 → r 0 = 0 →
        |fderiv ℝ (fderiv ℝ P) y v r| ≤ C / L ^ 2 * b * ‖v‖ * ‖r‖) ∧
      (∀ v r, v 0 = 0 → r 0 = 0 →
        |fderiv ℝ (fderiv ℝ P) y v r| ≤ C / L * ‖v‖ * ‖r‖) := by
  obtain ⟨C, hC, HC⟩ := exists_stableCorrectedRemainder_amplitude_bounds
  refine ⟨C + 40, by positivity, ?_⟩
  intro y hm hu hw
  obtain ⟨hr1, hrM, hr2, hrMz, hrMM⟩ := HC y hm hu hw
  obtain ⟨hpM, hpz, hpMM, hpMz, hpzz⟩ := stableCorrectedPhase_directional_bounds hm
  obtain ⟨hd1, hd2⟩ := stableBoundaryProjection_derivative_decomposition hm hu hw
  let b := |y 1| + |y 2|
  let L := y 0 + 1
  let Q := fun z : StableState => stableCorrectedPhase (z 0) (z 1) (z 2)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL : 0 < L := by linarith
  have hsmall (p q n : ℕ) (hpq : q ≤ p) (hn : n ≤ 3) :
      C / L ^ 3 * b ^ p ≤ C / L ^ n * b ^ q :=
    mul_le_mul (div_le_div_of_nonneg_left hC.le (pow_pos hL n) (pow_le_pow_right₀ hL1 hn))
      (pow_le_pow_of_le_one hb hb1 hpq) (by positivity) (by positivity)
  dsimp only
  rw [hd1, hd2]
  simp only [add_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv1 hv2
    have R := hrM v hv1 hv2
    have S := hpM v hv1 hv2
    have B := mul_le_mul_of_nonneg_right (hsmall 4 2 2 (by norm_num) (by norm_num)) (norm_nonneg v)
    have H := abs_add_le (fderiv ℝ stableCorrectedRemainder y v) (fderiv ℝ Q y v - v 0)
    have hpos : 0 ≤ (1 / L ^ 2) * b ^ 2 * ‖v‖ := by positivity
    dsimp only [L, b, Q] at B H hpos
    simp only [div_eq_mul_inv, one_mul] at R S B hpos ⊢
    rw [add_sub_assoc]
    nlinarith only [R, S, B, H, hpos]
  · intro v hv0
    have R := hr1 v
    have S := hpz v hv0
    have B := mul_le_mul_of_nonneg_right (hsmall 3 1 1 (by norm_num) (by norm_num)) (norm_nonneg v)
    have H := abs_add_le (fderiv ℝ stableCorrectedRemainder y v) (fderiv ℝ Q y v)
    have hpos : 0 ≤ (1 / L) * b * ‖v‖ := by positivity
    dsimp only [L, b, Q] at B H hpos
    simp only [div_eq_mul_inv, pow_one, one_mul] at R S B hpos ⊢
    nlinarith only [R, S, B, H, hpos]
  · intro v r hv1 hv2 hr1' hr2'
    have R := hrMM v r hv1 hv2 hr1' hr2'
    have S := hpMM v r hv1 hv2 hr1' hr2'
    have B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hsmall 4 2 3 (by norm_num) (le_refl 3)) (norm_nonneg v)) (norm_nonneg r)
    have H := abs_add_le (fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v r) (fderiv ℝ (fderiv ℝ Q) y v r)
    have hpos : 0 ≤ (1 / L ^ 3) * b ^ 2 * ‖v‖ * ‖r‖ := by positivity
    dsimp only [L, b, Q] at B H hpos
    simp only [div_eq_mul_inv, one_mul] at R S B hpos ⊢
    nlinarith only [R, S, B, H, hpos]
  · intro v r hv1 hv2 hr0
    have R := hrMz v r hv1 hv2
    have S := hpMz v r hv1 hv2 hr0
    have B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hsmall 3 1 2 (by norm_num) (by norm_num)) (norm_nonneg v)) (norm_nonneg r)
    have H := abs_add_le (fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v r) (fderiv ℝ (fderiv ℝ Q) y v r)
    have hpos : 0 ≤ (1 / L ^ 2) * b * ‖v‖ * ‖r‖ := by positivity
    dsimp only [L, b, Q] at B H hpos
    simp only [div_eq_mul_inv, pow_one, one_mul] at R S B hpos ⊢
    nlinarith only [R, S, B, H, hpos]
  · intro v r hv0 hr0
    have R := hr2 v r
    have S := hpzz v r hv0 hr0
    have B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hsmall 2 0 1 (by norm_num) (by norm_num)) (norm_nonneg v)) (norm_nonneg r)
    have H := abs_add_le (fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v r) (fderiv ℝ (fderiv ℝ Q) y v r)
    have hpos : 0 ≤ (1 / L) * ‖v‖ * ‖r‖ := by positivity
    dsimp only [L, b, Q] at B H hpos
    simp only [div_eq_mul_inv, pow_one, pow_zero, mul_one, one_mul] at R S B hpos ⊢
    nlinarith only [R, S, B, H, hpos]
