-- Prove2me | solution 1 for BianchiIX.stableBoundaryHessian_mixed_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T15:12:46.236919+00:00
-- url     : https://prove2.me/submissions/fd040395-44cb-41fb-9828-f04e12a41329

import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Theorems.Thm_BianchiIX_stableBoundaryHessian_norm_bound
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.hasDerivAt_fderiv_apply_const {f : E → F} {gamma : ℝ → E} {v : E} {t : ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (gamma t))
    (hg : HasDerivAt gamma v t) (w : E) :
    HasDerivAt (fun s => fderiv ℝ f (gamma s) w)
      (fderiv ℝ (fderiv ℝ f) (gamma t) v w) t := by
  have H := (hf.hasFDerivAt.comp_hasDerivAt t hg).clm_apply (hasDerivAt_const t w)
  simpa only [Function.comp_apply, ContinuousLinearMap.map_zero, add_zero] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableBoundaryField (n : WithTop ℕ∞) : ContDiff ℝ n stableBoundaryField := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [stableBoundaryField, stableStrongRate, stableWeakRate] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableBoundaryField {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) :
    HasDerivAt (fun s => stableBoundaryField (gamma s))
      ((stableBoundaryJacobian (gamma t)).mulVec v) t := by
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply (((hm.mul (hu.pow 2)).sub (((hm.add_const 1).mul hu).mul hw)).add
      (hw.pow 2)).congr_deriv
    simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · apply ((((((hasDerivAt_const t (1 : ℝ)).sub (hm.pow 2)).sub
      (hw.pow 2)).add (hu.pow 2)).div_const 2).mul hu).congr_deriv
    simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · apply ((((hm.add_const 1).add (hu.mul hw)).sub (hu.pow 2)).neg.mul hw).congr_deriv
    simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryField_fderiv (y v : StableState) :
    fderiv ℝ stableBoundaryField y v = (stableBoundaryJacobian y).mulVec v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hf := ((contDiff_stableBoundaryField 1).differentiable (by norm_num) y).hasFDerivAt
  have hzero : y + (0 : ℝ) • v = y := by simp
  have H := (hzero.symm ▸ hf).comp_hasDerivAt 0 hl
  simpa only [hzero] using H.unique (hasDerivAt_stableBoundaryField hl)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryJacobian_mulVec (y v : StableState) :
    (stableBoundaryJacobian y).mulVec v =
      ![(y 1 ^ 2 - y 1 * y 2) * v 0 + (2 * y 0 * y 1 - (y 0 + 1) * y 2) * v 1 +
          (-(y 0 + 1) * y 1 + 2 * y 2) * v 2,
        (-y 0 * y 1) * v 0 + ((1 - y 0 ^ 2 - y 2 ^ 2 + 3 * y 1 ^ 2) / 2) * v 1 +
          (-y 1 * y 2) * v 2,
        -y 2 * v 0 + (2 * y 1 - y 2) * y 2 * v 1 -
          (y 0 + 1 + 2 * y 1 * y 2 - y 1 ^ 2) * v 2] := by
  ext i
  fin_cases i <;> simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableBoundaryJacobian_mulVec
    {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (w : StableState) :
    HasDerivAt (fun s => (stableBoundaryJacobian (gamma s)).mulVec w)
      (stableBoundaryHessian (gamma t) v w) t := by
  simp only [stableBoundaryJacobian_mulVec]
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply ((((hu.pow 2).sub (hu.mul hw)).mul_const (w 0)).add
      ((((hm.const_mul 2).mul hu).sub ((hm.add_const 1).mul hw)).mul_const (w 1)) |>.add
      ((((hm.add_const 1).neg.mul hu).add (hw.const_mul 2)).mul_const (w 2))).congr_deriv
    dsimp [stableBoundaryHessian]
    ring
  · apply (((hm.neg.mul hu).mul_const (w 0)).add
      ((((((hasDerivAt_const t (1 : ℝ)).sub (hm.pow 2)).sub (hw.pow 2)).add
        ((hu.pow 2).const_mul 3)).div_const 2).mul_const (w 1)) |>.add
      ((hu.neg.mul hw).mul_const (w 2))).congr_deriv
    dsimp [stableBoundaryHessian]
    ring
  · apply (((hw.neg.mul_const (w 0)).add
      ((((hu.const_mul 2).sub hw).mul hw).mul_const (w 1))).sub
      ((((hm.add_const 1).add (((hu.const_mul 2).mul hw))).sub (hu.pow 2)).mul_const (w 2))).congr_deriv
    dsimp [stableBoundaryHessian]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryField_fderiv2 (y v w : StableState) :
    fderiv ℝ (fderiv ℝ stableBoundaryField) y v w = stableBoundaryHessian y v w := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hD : Differentiable ℝ (fderiv ℝ stableBoundaryField) :=
    ((contDiff_stableBoundaryField 2).fderiv_right
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have H := hasDerivAt_fderiv_apply_const (hD (y + (0 : ℝ) • v)) hl w
  simp only [stableBoundaryField_fderiv] at H
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_stableBoundaryJacobian_mulVec hl w)

end
end

private theorem BianchiIX.stableTangent_split_bounds (v : StableState) :
    ‖(![v 0, 0, 0] : StableState)‖ ≤ ‖v‖ ∧
      ‖(![0, v 1, v 2] : StableState)‖ ≤ ‖![v 1, v 2]‖ ∧ ‖![v 1, v 2]‖ ≤ ‖v‖ := by
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 0
    · simp
    · simp
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · simp
    · exact norm_le_pi_norm ![v 1, v 2] 0
    · exact norm_le_pi_norm ![v 1, v 2] 1
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 1
    · exact norm_le_pi_norm v 2

theorem solution {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    ‖stableBoundaryHessian y v w‖ ≤ (|y 1| + |y 2|) * ‖v‖ * ‖w‖ +
      12 * (c + 1) * (‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖) := by
  let vc : StableState := ![v 0, 0, 0]
  let vz : StableState := ![0, v 1, v 2]
  let wc : StableState := ![w 0, 0, 0]
  let wz : StableState := ![0, w 1, w 2]
  let B := fderiv ℝ (fderiv ℝ stableBoundaryField) y
  have hvsum : vc + vz = v := by ext i; fin_cases i <;> simp [vc, vz]
  have hwsum : wc + wz = w := by ext i; fin_cases i <;> simp [wc, wz]
  have hv := stableTangent_split_bounds v
  have hw' := stableTangent_split_bounds w
  have hdecomp : stableBoundaryHessian y v w = stableBoundaryHessian y vc wc +
      stableBoundaryHessian y vz w + stableBoundaryHessian y vc wz := by
    simp only [← stableBoundaryField_fderiv2]
    change B v w = B vc wc + B vz w + B vc wz
    have Hv : B v w = B vc w + B vz w := by rw [← hvsum, map_add, add_apply]
    have Hw : B vc w = B vc wc + B vc wz := by rw [← hwsum, map_add]
    rw [Hv, Hw]
    abel
  have hcc : ‖stableBoundaryHessian y vc wc‖ ≤ (|y 1| + |y 2|) * ‖v‖ * ‖w‖ := by
    have hp := mul_le_mul (norm_le_pi_norm v 0) (norm_le_pi_norm w 0) (norm_nonneg _) (norm_nonneg _)
    simp only [Real.norm_eq_abs] at hp
    have H := mul_le_mul (show |y 1| ≤ |y 1| + |y 2| by linarith [abs_nonneg (y 2)])
      hp (by positivity) (by positivity)
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · simp [stableBoundaryHessian, vc, wc]
      positivity
    · simpa [stableBoundaryHessian, vc, wc, Real.norm_eq_abs, abs_mul, mul_assoc] using H
    · simp [stableBoundaryHessian, vc, wc]
      positivity
  have hleft := (stableBoundaryHessian_norm_bound hc hm hu hw vz w).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hv.2.1 (by positivity : 0 ≤ 12 * (c + 1))) (norm_nonneg w))
  have hright := (stableBoundaryHessian_norm_bound hc hm hu hw vc wz).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hv.1 (by positivity : 0 ≤ 12 * (c + 1))) hw'.2.1
      (norm_nonneg _) (by positivity))
  rw [hdecomp]
  have H := (norm_add_le (stableBoundaryHessian y vc wc + stableBoundaryHessian y vz w)
    (stableBoundaryHessian y vc wz)).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
  nlinarith only [H, hcc, hleft, hright]
