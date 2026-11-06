-- Prove2me | solution 1 for BianchiIX.hasDerivAt_coreClockProjection
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:43:27.815667+00:00
-- url     : https://prove2.me/submissions/ae5b674a-9b73-46fb-a47d-7c2f9970b319

import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Definitions.Def_BianchiIX_Dynamics_CoreLinearization
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Theorems.Thm_BianchiIX_contDiffAt_projectiveOriginalField
import Theorems.Thm_BianchiIX_contDiff_projectiveStateDenom
import Theorems.Thm_BianchiIX_hasDerivAt_coordinate_clock_variation
import Theorems.Thm_BianchiIX_hasDerivAt_coreAngleField
import Theorems.Thm_BianchiIX_projectiveCoreAngle_fderiv_field
import Theorems.Thm_BianchiIX_toCoreAngleState_fderiv_field
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.tanh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.tanh (coreAngle m v) = (1 - m) / coreRadius m v := by
  rw [coreAngle, Real.tanh_arsinh, coreAngle_sqrt hv]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_coordinates {m v : ℝ} (hv : 0 < v) :
    coreRadius m v / Real.cosh (coreAngle m v) = v ∧
      1 - coreRadius m v * Real.tanh (coreAngle m v) = m := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  rw [cosh_coreAngle hv, tanh_coreAngle hv]
  constructor
  · field_simp
  · field_simp
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreAngle (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n projectiveCoreAngle y := by
  have hv0 := ne_of_gt hv
  unfold projectiveCoreAngle coreAngle
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreRadius (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
  have he : coreEnergy (y 0) (y 2) ≠ 0 := by unfold coreEnergy; positivity
  have he' : (y 0 - 1) ^ 2 + y 2 ^ 2 ≠ 0 := he
  unfold coreRadius coreEnergy
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_toCoreAngleState (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n toCoreAngleState y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [toCoreAngleState] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreClockFactor (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) :
    ContDiffAt ℝ n (fun z : ProjectiveState =>
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  have hr2 : coreRadius (y 0) (y 2) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (coreRadius_pos hv))
  unfold coreClockFactor
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_coreOriginalClockRate (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) (hD : projectiveStateDenom y ≠ 0) :
    ContDiffAt ℝ n coreOriginalClockRate y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  have hr2 : coreRadius (y 0) (y 2) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (coreRadius_pos hv))
  have hden := (contDiff_projectiveStateDenom n).contDiffAt (x := y)
  unfold coreOriginalClockRate coreClockFactor
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_coreAuxiliary (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) : ContDiffAt ℝ n (coreAuxiliary z) y := by
  have hv : y 0 / Real.cosh z ≠ 0 := div_ne_zero hr (ne_of_gt (Real.cosh_pos z))
  have hr2 : y 0 ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr' : 2 * y 0 ≠ 0 := mul_ne_zero (by norm_num) hr
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreAuxiliary, coupling, coreClockFactor] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_coreAuxiliary_joint (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) :
    ContDiffAt ℝ n (fun p : ℝ × CoreAngleState => coreAuxiliary p.1 p.2) (z, y) := by
  have hz : Real.cosh z ≠ 0 := ne_of_gt (Real.cosh_pos z)
  have hv : y 0 / Real.cosh z ≠ 0 := div_ne_zero hr hz
  have hr2 : y 0 ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr' : 2 * y 0 ≠ 0 := mul_ne_zero (by norm_num) hr
  have ht : ContDiffAt ℝ n (fun p : ℝ × CoreAngleState => Real.tanh p.1) (z, y) := by
    simp_rw [Real.tanh_eq_sinh_div_cosh]
    fun_prop
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreAuxiliary, coupling, coreClockFactor] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngleField_auxiliary (z : ℝ) (y : CoreAngleState) :
    coreAngleField z y = ![(coreAuxiliary z y) 3 / (coreAuxiliary z y) 1,
      y 1 * (coreAuxiliary z y) 2 / (coreAuxiliary z y) 1,
      -2 * y 2 * (1 + (coreAuxiliary z y) 0) / (y 0 * (coreAuxiliary z y) 1)] := rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_coreAngleField (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : (coreAuxiliary z y) 1 ≠ 0) :
    ContDiffAt ℝ n (coreAngleField z) y := by
  have hq := contDiffAt_pi.mp (contDiffAt_coreAuxiliary n z hr)
  have hrd : y 0 * (coreAuxiliary z y) 1 ≠ 0 := mul_ne_zero hr hd
  apply contDiffAt_pi.mpr
  intro i
  simp_rw [coreAngleField_auxiliary]
  fin_cases i <;> dsimp <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_coreAngleField_joint (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : (coreAuxiliary z y) 1 ≠ 0) :
    ContDiffAt ℝ n (fun p : ℝ × CoreAngleState => coreAngleField p.1 p.2) (z, y) := by
  have hq := contDiffAt_pi.mp (contDiffAt_coreAuxiliary_joint n z hr)
  have hrd : y 0 * (coreAuxiliary z y) 1 ≠ 0 := mul_ne_zero hr hd
  apply contDiffAt_pi.mpr
  intro i
  simp_rw [coreAngleField_auxiliary]
  fin_cases i <;> dsimp <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngleField_fderiv (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : (coreAuxiliary z y) 1 ≠ 0) (ξ : CoreAngleState) :
    fderiv ℝ (coreAngleField z) y ξ = (coreAngleJacobian z y).mulVec ξ := by
  have hl : HasDerivAt (fun s : ℝ => y + s • ξ) ξ 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const ξ) using 1
    simp
  have hzero : y + (0 : ℝ) • ξ = y := by simp
  have hf := ((contDiffAt_coreAngleField 1 z hr hd).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hzero.symm ▸ hf).comp_hasDerivAt 0 hl
  simpa only [hzero] using H.unique (hasDerivAt_coreAngleField hl
    (by simpa only [hzero] using hr) (by simpa only [hzero] using hd))

end
end

private theorem BianchiIX.coreAuxiliary_projective_clockFactor {y : ProjectiveState} (hv : 0 < y 2) :
    coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 1 =
      coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) := by
  change coreClockFactor (coreRadius (y 0) (y 2)) (y 1)
    (y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))) = _
  rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ (ne_of_gt hv)]

theorem solution {beta v : ℝ → ProjectiveState} {t : ℝ}
    (hbeta : HasDerivAt beta (projectiveOriginalField (beta t)) t)
    (hv : HasDerivAt v (fderiv ℝ projectiveOriginalField (beta t) (v t)) t)
    (hV : 0 < beta t 2) (hD : projectiveStateDenom (beta t) ≠ 0)
    (hd : coreClockFactor (coreRadius (beta t 0) (beta t 2)) (beta t 1) (beta t 3) ≠ 0) :
    HasDerivAt (fun s => coreClockProjection (beta s) (v s))
      (coreOriginalClockRate (beta t) •
        (coreAngleJacobian (projectiveCoreAngle (beta t)) (toCoreAngleState (beta t))).mulVec
          (coreClockProjection (beta t) (v t))) t := by
  have hr : (toCoreAngleState (beta t)) 0 ≠ 0 := ne_of_gt (coreRadius_pos hV)
  have hd' : coreAuxiliary (projectiveCoreAngle (beta t)) (toCoreAngleState (beta t)) 1 ≠ 0 := by
    rw [coreAuxiliary_projective_clockFactor hV]
    exact hd
  have hVnear : ∀ᶠ y : ProjectiveState in 𝓝 (beta t), 0 < y 2 :=
    (continuous_apply 2).continuousAt.eventually (isOpen_Ioi.mem_nhds hV)
  have hdnear := (contDiffAt_projectiveCoreClockFactor 1 hV).continuousAt.eventually_ne hd
  have hclock : (fun y => fderiv ℝ projectiveCoreAngle y (projectiveOriginalField y))
      =ᶠ[𝓝 (beta t)] coreOriginalClockRate := by
    filter_upwards [hVnear] with y hy
    exact projectiveCoreAngle_fderiv_field hy
  have hstate : (fun y => fderiv ℝ toCoreAngleState y (projectiveOriginalField y))
      =ᶠ[𝓝 (beta t)] (fun y => coreOriginalClockRate y •
        coreAngleField (projectiveCoreAngle y) (toCoreAngleState y)) := by
    filter_upwards [hVnear, hdnear] with y hy hdy
    exact toCoreAngleState_fderiv_field hy hdy
  have H := hasDerivAt_coordinate_clock_variation
    (contDiffAt_toCoreAngleState 2 hV) (contDiffAt_projectiveCoreAngle 2 hV)
    ((contDiffAt_projectiveOriginalField 1 hD).differentiableAt (by norm_num))
    ((contDiffAt_coreOriginalClockRate 1 hV hD).differentiableAt (by norm_num))
    ((contDiffAt_coreAngleField_joint 1 (projectiveCoreAngle (beta t)) hr hd').differentiableAt
      (by norm_num)) hbeta hv hclock hstate
  change HasDerivAt (fun s => coreClockProjection (beta s) (v s))
    (coreOriginalClockRate (beta t) •
      fderiv ℝ (coreAngleField (projectiveCoreAngle (beta t))) (toCoreAngleState (beta t))
        (coreClockProjection (beta t) (v t))) t at H
  rw [coreAngleField_fderiv _ hr hd'] at H
  exact H
