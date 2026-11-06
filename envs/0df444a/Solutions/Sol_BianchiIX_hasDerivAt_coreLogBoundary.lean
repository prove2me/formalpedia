-- Prove2me | solution 1 for BianchiIX.hasDerivAt_coreLogBoundary
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:02:27.55513+00:00
-- url     : https://prove2.me/submissions/4dba5ea1-34d6-405e-9d36-178184dd19d8

import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreLogIntegralVariation
import Theorems.Thm_BianchiIX_contDiffAt_coreLogRates_joint
import Theorems.Thm_BianchiIX_contDiffAt_coreOriginalLogRates
import Theorems.Thm_BianchiIX_contDiffAt_projectiveOriginalField
import Theorems.Thm_BianchiIX_contDiff_projectiveStateDenom
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_clock_integral_boundary
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_projectiveCoreAngle_fderiv_field
import Theorems.Thm_BianchiIX_toCoreAngleState_fderiv_field
import Theorems.Thm_BianchiIX_toProjectiveState_denom_pos
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
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
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
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

private theorem BianchiIX.contDiffAt_coreLogRates (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : coreAuxiliary z y 1 ≠ 0) : ContDiffAt ℝ n (coreLogRates z) y := by
  have hq := contDiffAt_pi.mp (contDiffAt_coreAuxiliary n z hr)
  have hrd : y 0 * coreAuxiliary z y 1 ≠ 0 := mul_ne_zero hr hd
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreLogRates] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_projectiveOriginalFlow_time {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasDerivAt (projectiveOriginalFlow y t₀)
      (projectiveOriginalField (projectiveOriginalFlow y t₀ t)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_projectiveOriginalFlow (hasDerivAt_normalizedMaxCurve ht) (ne_of_gt hA) hc

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreAuxiliary_projective_clockFactor {y : ProjectiveState} (hv : 0 < y 2) :
    coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 1 =
      coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) := by
  change coreClockFactor (coreRadius (y 0) (y 2)) (y 1)
    (y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))) = _
  rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ (ne_of_gt hv)]

end
end

/-- The physical clock variation is exactly a total derivative, without wall division. -/
theorem solution {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y)
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hV : 0 < projectiveOriginalFlow y t₀ t 2)
    (hd : coreClockFactor (coreRadius (projectiveOriginalFlow y t₀ t 0)
      (projectiveOriginalFlow y t₀ t 2)) (projectiveOriginalFlow y t₀ t 1)
        (projectiveOriginalFlow y t₀ t 3) ≠ 0) (w : ProjectiveState) (i : Fin 2) :
    let z := projectiveOriginalFlow y t₀ t
    let v := projectiveFlowDifferential y t₀ t w
    HasDerivAt (fun s => coreLogBoundary y t₀ s w i)
      ((fderiv ℝ coreOriginalLogRates z v) i - coreOriginalClockRate z *
        (fderiv ℝ (coreLogRates (projectiveCoreAngle z)) (toCoreAngleState z)
          (coreProjectedFlowVariation y t₀ t w)) i) t := by
  intro z v
  have hc := (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have hDz : projectiveStateDenom z ≠ 0 := ne_of_gt (toProjectiveState_denom_pos hA hc)
  have hr : toCoreAngleState z 0 ≠ 0 := ne_of_gt (coreRadius_pos hV)
  have hd' : coreAuxiliary (projectiveCoreAngle z) (toCoreAngleState z) 1 ≠ 0 := by
    rwa [coreAuxiliary_projective_clockFactor hV]
  have hclock : (fun x => fderiv ℝ projectiveCoreAngle x (projectiveOriginalField x)) =ᶠ[𝓝 z]
      coreOriginalClockRate := by
    filter_upwards [(continuous_apply 2).continuousAt.eventually (isOpen_Ioi.mem_nhds hV)] with x hx
    exact projectiveCoreAngle_fderiv_field hx
  have hLc := contDiffAt_pi.mp (contDiffAt_coreLogRates_joint 1 (projectiveCoreAngle z) hr hd') i
  have hL := hLc.differentiableAt (by norm_num)
  have H := hasDerivAt_clock_integral_boundary
    ((contDiffAt_toCoreAngleState 1 hV).differentiableAt (by norm_num))
    (contDiffAt_projectiveCoreAngle 2 hV)
    ((contDiffAt_projectiveOriginalField 1 hDz).differentiableAt (by norm_num))
    ((contDiffAt_coreOriginalClockRate 1 hV hDz).differentiableAt (by norm_num)) hL
    (hasDerivAt_projectiveOriginalFlow_time hD ht hA)
    (hasDerivAt_projectiveFlowDifferential_apply hD ht hA w) hclock
    (toCoreAngleState_fderiv_field hV hd)
  have hrate := (contDiffAt_coreOriginalLogRates 1 hV hDz hd).differentiableAt (by norm_num)
  have hslice := (contDiffAt_coreLogRates 1 (projectiveCoreAngle z) hr hd').differentiableAt (by norm_num)
  apply H.congr_deriv
  change fderiv ℝ (fun q => coreOriginalLogRates q i) z v - coreOriginalClockRate z *
    fderiv ℝ (fun X => coreLogRates (projectiveCoreAngle z) X i) (toCoreAngleState z)
      (coreProjectedFlowVariation y t₀ t w) = _
  rw [fderiv_apply hrate i, fderiv_apply hslice i]
  rfl
