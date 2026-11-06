-- Prove2me | solution 1 for BianchiIX.partialCoreReturn_log_derivative_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:32:36.3717+00:00
-- url     : https://prove2.me/submissions/97da123c-ffdb-4c02-ac8b-4e364bcccb79

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_coreRegion_exit_angle_bound
import Theorems.Thm_BianchiIX_coreRegion_log_rate_bounds
import Theorems.Thm_BianchiIX_exists_coreExit_event
import Theorems.Thm_BianchiIX_partialCoreReturn_log_derivative
import Theorems.Thm_BianchiIX_partialCore_log_integral_bounds
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.core_log_lower_bound {k : ℝ} (hk : 6 ≤ k) : 1 ≤ Real.log (4 * k) := by
  have H := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at H
  exact H.trans (Real.log_le_log (by norm_num) (by linarith only [hk]))

end
end

private theorem BianchiIX.partialCoreReturn_exit_angle_bound {k : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContinuousAt τ y) (ht : τ y ∈ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 (τ y) 0)
    (hcore : coreRegion k (projectiveOriginalFlow y 0 (τ y)))
    (hhit : ∀ᶠ x in 𝓝 y, projectiveOriginalFlow x 0 (τ x) 2 = 1)
    (hM : projectiveOriginalFlow y 0 (τ y) 0 < 1) (w : ProjectiveState) :
    |fderiv ℝ (fun x => projectiveCoreAngle (projectiveOriginalFlow x 0 (τ x))) y w| ≤
      2 * |coreProjectedFlowVariation y 0 (τ y) w 0| / k := by
  have hV := hhit.self_of_nhds
  obtain ⟨σ, _, _, _, huniq, _, _, hderiv⟩ :=
    exists_coreExit_event hk hD ht hA hcore hV hM
  have hpair : ContinuousAt (fun x => (x, τ x)) y := continuousAt_id.prodMk hτ
  have heq : (fun x => projectiveCoreAngle (projectiveOriginalFlow x 0 (τ x))) =ᶠ[𝓝 y]
      (fun x => projectiveCoreAngle (projectiveOriginalFlow x 0 (σ x))) := by
    filter_upwards [hpair.eventually huniq, hhit] with x hx hh
    rw [(hx.2.mp hh).symm]
  rw [heq.fderiv_eq, (hderiv w).1]
  exact coreRegion_exit_angle_bound hk hcore hV hM _


/-- Arbitrary interior entrances retain the initial-angle term in (E.23). -/
theorem solution {k Q : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContDiffAt ℝ 1 τ y) (hpos : 0 ≤ τ y)
    (hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t))
    (hhit : ∀ᶠ x in 𝓝 y, projectiveOriginalFlow x 0 (τ x) 2 = 1)
    (hM : projectiveOriginalFlow y 0 (τ y) 0 < 1) (w : ProjectiveState)
    (hnorm : ∀ t ∈ Icc 0 (τ y), ‖scaleCoreVariation k (coreProjectedFlowVariation y 0 t w)‖ ≤ Q) :
    |fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x 0)) y w| ≤
      10 * Real.log (4 * k) * Q + 2 * k * |fderiv ℝ projectiveCoreAngle y w| ∧
    |fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x 1)) y w| ≤
      59 * Real.log (4 * k) * Q / k ^ 2 + 4 * |fderiv ℝ projectiveCoreAngle y w| / k := by
  have hk0 : 0 < k := by linarith only [hk]
  let β := projectiveOriginalFlow y 0
  let ξ := fun t => coreProjectedFlowVariation y 0 t w
  let L := fun t => coreLogRates (projectiveCoreAngle (β t)) (toCoreAngleState (β t))
  let I := fun i : Fin 2 => ∫ t in 0..τ y, coreOriginalClockRate (β t) *
    (fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t)) (ξ t)) i
  let a := fderiv ℝ projectiveCoreAngle y w
  let b := fderiv ℝ (fun x => projectiveCoreAngle (projectiveOriginalFlow x 0 (τ x))) y w
  have hstart : (0 : ℝ) ∈ Icc 0 (τ y) := ⟨le_rfl, hpos⟩
  have hend : τ y ∈ Icc 0 (τ y) := ⟨hpos, le_rfl⟩
  have hQ : 0 ≤ Q := (norm_nonneg _).trans (hnorm 0 hstart)
  have hI : |I 0| ≤ 6 * Real.log (4 * k) * Q ∧ |I 1| ≤ 51 * Real.log (4 * k) * Q / k ^ 2 :=
    partialCore_log_integral_bounds hk hpos hD hdom hA hcore w hnorm
  have hb : |b| ≤ 2 * Q / k := by
    have H := partialCoreReturn_exit_angle_bound hk hD hτ.continuousAt (hdom hend)
      (hA _ hend) (hcore _ hend) hhit hM w
    have hr : |ξ (τ y) 0| ≤ Q :=
      (norm_le_pi_norm (scaleCoreVariation k (ξ (τ y))) 0).trans (hnorm _ hend)
    exact H.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by norm_num)) hk0.le)
  have hLa := coreRegion_log_rate_bounds hk (hcore 0 hstart)
  have hLb := coreRegion_log_rate_bounds hk (hcore (τ y) hend)
  have ha0 : |L 0 0 * a| ≤ 2 * k * |a| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hLa.1 (abs_nonneg _)
  have hb0 : |L (τ y) 0 * b| ≤ 4 * Q := by
    rw [abs_mul]
    exact (mul_le_mul hLb.1 hb (abs_nonneg _) (by positivity)).trans_eq (by field_simp; ring)
  have ha1 : |L 0 1 * a| ≤ 4 * |a| / k := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hLa.2.1 (abs_nonneg _)).trans_eq (by ring)
  have hb1 : |L (τ y) 1 * b| ≤ 8 * Q / k ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hLb.2.1 hb (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hderiv (i : Fin 2) :
      fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x i)) y w =
        I i + L (τ y) i * b - L 0 i * a :=
    partialCoreReturn_log_derivative hk hD hτ hpos hdom hA hcore w i
  have htri (i : Fin 2) : |fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x i)) y w| ≤
      |I i| + |L (τ y) i * b| + |L 0 i * a| := by
    rw [hderiv]
    exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
  have hlogQ : Q ≤ Real.log (4 * k) * Q := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (core_log_lower_bound hk) hQ
  constructor
  · exact (htri 0).trans ((add_le_add (add_le_add hI.1 hb0) ha0).trans (by nlinarith only [hlogQ]))
  · apply (htri 1).trans ((add_le_add (add_le_add hI.2 hb1) ha1).trans ?_)
    apply add_le_add_left
    calc
      _ = (51 * Real.log (4 * k) * Q + 8 * Q) / k ^ 2 := by ring
      _ ≤ (59 * Real.log (4 * k) * Q) / k ^ 2 :=
        div_le_div_of_nonneg_right (by nlinarith only [hlogQ]) (sq_nonneg _)
