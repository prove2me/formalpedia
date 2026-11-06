-- Prove2me | solution 1 for BianchiIX.partialCoreReturn_log_derivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:30:52.141211+00:00
-- url     : https://prove2.me/submissions/712e8700-c831-4f49-918a-e733eaebe776

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreLogIntegralVariation
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_contDiffAt_coreOriginalLogRates
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreFlow_log_rate_integral_variation
import Theorems.Thm_BianchiIX_fderiv_moving_intervalIntegral
import Theorems.Thm_BianchiIX_fderiv_variable_endpoint
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_coreAngle_scaled
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedFlowDifferential_initial (x : NormalizedState) (t₀ : ℝ) :
    normalizedFlowDifferential x t₀ t₀ = ContinuousLinearMap.id ℝ NormalizedState := by
  simp [normalizedFlowDifferential, normalizedMaxCurve_initial]

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology ContDiff

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_smooth {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ ∞ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  contDiffAt_infty.mpr (fun n => contDiffAt_normalizedMaxCurve_nat n ht)

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
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_two {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  (contDiffAt_normalizedMaxCurve_smooth ht).of_le (by decide)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveOriginalFlow_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveOriginalFlow y t₀ t₀ = y := by
  rw [projectiveOriginalFlow, normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt hD)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveFlowDifferential_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveFlowDifferential y t₀ t₀ = ContinuousLinearMap.id ℝ ProjectiveState := by
  rw [projectiveFlowDifferential, normalizedMaxCurve_initial, normalizedFlowDifferential_initial,
    ContinuousLinearMap.id_comp, projective_chart_differential_inverse hD]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_projectiveOriginalFlow_initial {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasFDerivAt (fun z => projectiveOriginalFlow z t₀ t) (projectiveFlowDifferential y t₀ t) y := by
  have hfrom := ((contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).differentiableAt (by norm_num)).hasFDerivAt
  have hto := ((contDiffAt_toProjectiveState 1 (ne_of_gt hA)).differentiableAt (by norm_num)).hasFDerivAt
  exact hto.comp y ((hasFDerivAt_normalizedMaxCurve_initial ht).comp y hfrom)

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
open Set

private theorem BianchiIX.contDiffAt_projectiveOriginalFlow_two {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2) (y, t) := by
  have hparam : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => (fromProjectiveState z.1, z.2)) (y, t) :=
    ((contDiffAt_fromProjectiveState 2 (ne_of_gt hD)).comp (y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hN : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => normalizedMaxCurve (fromProjectiveState z.1) t₀ z.2) (y, t) := by
    simpa only [Function.comp_def] using (contDiffAt_normalizedMaxCurve_two ht).comp (y, t) hparam
  simpa only [Function.comp_def, projectiveOriginalFlow] using
    (contDiffAt_toProjectiveState 2 (ne_of_gt hA)).comp (y, t) hN

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_radius_bounds {k : ℝ} {y : ProjectiveState} (hk : 6 ≤ k) (hy : coreRegion k y) :
    99 / 100 * k ≤ coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) ≤ 101 / 100 * k :=
  coreBootstrap_radius_closed hk (Real.sqrt_nonneg _)
    (by rw [coreRadius_sq]; exact hy.1)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_wall_bounds {k : ℝ} {y : ProjectiveState} (hy : coreRegion k y) :
    (0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k) ∧ (0 ≤ y 3 ∧ y 3 ≤ (1 / 10000) / k) := by
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hw0 : 0 ≤ y 3 := (mul_nonneg_iff_of_pos_left hv0).mp hy.2.2.2.1
  exact ⟨hy.2.2.1, hw0, (le_mul_of_one_le_left hw0 hy.2.1).trans hy.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreRegion_clock_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    0 < projectiveStateDenom y ∧
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ∧
        0 < coreOriginalClockRate y := by
  have hk0 : 0 < k := by linarith only [hk]
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hD := coreBootstrap_denom_lower (m := y 0) (v := y 2) hk hu hw
  have hd := (coreBootstrap_clock_bounds hk hr.1 hu hw).1
  have hrate := coreBootstrap_original_clock_lower hk hr (zero_le_one.trans hy.2.1) hu hw
  exact ⟨lt_of_lt_of_le (by norm_num) hD, lt_of_lt_of_le (by norm_num) hd,
    lt_of_lt_of_le (one_div_pos.mpr hk0) hrate⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.log_coreFlowMultiplier (y : ProjectiveState) (t₀ a b : ℝ) (i : Fin 2) :
    Real.log (coreFlowMultiplier y t₀ a b i) =
      ∫ t in a..b, coreOriginalLogRates (projectiveOriginalFlow y t₀ t) i :=
  Real.log_exp _

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_projectiveCoreLogRates {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y)
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hV : 0 < projectiveOriginalFlow y t₀ t 2)
    (hDz : projectiveStateDenom (projectiveOriginalFlow y t₀ t) ≠ 0)
    (hd : let z := projectiveOriginalFlow y t₀ t
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0) :
    ContDiffAt ℝ 1 (fun p : ProjectiveState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow p.1 t₀ p.2)) (y, t) :=
  (contDiffAt_coreOriginalLogRates 1 hV hDz hd).comp (y, t) (g := coreOriginalLogRates)
    (f := fun p : ProjectiveState × ℝ => projectiveOriginalFlow p.1 t₀ p.2)
    ((contDiffAt_projectiveOriginalFlow_two hD ht hA).of_le (by norm_num))

end
end

private theorem BianchiIX.projectiveCoreLogRate_parameter_derivative {y : ProjectiveState} {t : ℝ}
    (hD : 0 < projectiveStateDenom y)
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hV : 0 < projectiveOriginalFlow y 0 t 2)
    (hDz : projectiveStateDenom (projectiveOriginalFlow y 0 t) ≠ 0)
    (hd : let z := projectiveOriginalFlow y 0 t
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0)
    (w : ProjectiveState) (i : Fin 2) :
    fderiv ℝ (fun p : ProjectiveState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow p.1 0 p.2) i) (y, t) (w, 0) =
      (fderiv ℝ coreOriginalLogRates (projectiveOriginalFlow y 0 t)
        (projectiveFlowDifferential y 0 t w)) i := by
  have hFc := contDiffAt_pi.mp (contDiffAt_projectiveCoreLogRates hD ht hA hV hDz hd) i
  have hleft := (hFc.differentiableAt (by norm_num)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) y t)
  have hrate := hasFDerivAt_pi'.mp
    ((contDiffAt_coreOriginalLogRates 1 hV hDz hd).differentiableAt (by norm_num)).hasFDerivAt i
  have hright := hrate.comp y (hasFDerivAt_projectiveOriginalFlow_initial hD ht hA)
  exact congrArg (fun A : ProjectiveState →L[ℝ] ℝ => A w) (hleft.unique hright)

private theorem BianchiIX.partialCoreReturn_angle_derivative {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hD : 0 < projectiveStateDenom y) (hτ : DifferentiableAt ℝ τ y)
    (ht : τ y ∈ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 (τ y) 0)
    (hV : 0 < projectiveOriginalFlow y 0 (τ y) 2) (w : ProjectiveState) :
    let z := projectiveOriginalFlow y 0 (τ y)
    fderiv ℝ (fun x => projectiveCoreAngle (projectiveOriginalFlow x 0 (τ x))) y w =
      fderiv ℝ projectiveCoreAngle z (projectiveFlowDifferential y 0 (τ y) w) +
      coreOriginalClockRate z * fderiv ℝ τ y w := by
  intro z
  have hangle := (contDiffAt_projectiveCoreAngle 1 hV).differentiableAt (by norm_num)
  have hF := hangle.comp (y, τ y)
    ((contDiffAt_projectiveOriginalFlow_two hD ht hA).differentiableAt (by norm_num))
  have hleft := hangle.hasFDerivAt.comp y (hasFDerivAt_projectiveOriginalFlow_initial hD ht hA)
  have hright := hasDerivAt_coreAngle_scaled (hasDerivAt_projectiveOriginalFlow_time hD ht hA) hV
  exact fderiv_variable_endpoint hF hτ hleft hright w


/-- Fixed-angle variation accounts for the interior; both ordinary endpoint motions remain. -/
theorem solution {k : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContDiffAt ℝ 1 τ y) (hpos : 0 ≤ τ y)
    (hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t))
    (w : ProjectiveState) (i : Fin 2) :
    let β := projectiveOriginalFlow y 0
    let L := fun t => coreLogRates (projectiveCoreAngle (β t)) (toCoreAngleState (β t)) i
    fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x i)) y w =
      (∫ t in 0..τ y, coreOriginalClockRate (β t) *
        (fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t))
          (coreProjectedFlowVariation y 0 t w)) i) +
      L (τ y) * fderiv ℝ (fun x => projectiveCoreAngle (projectiveOriginalFlow x 0 (τ x))) y w -
      L 0 * fderiv ℝ projectiveCoreAngle y w := by
  intro β L
  have hV (t : ℝ) (ht : t ∈ Icc 0 (τ y)) : 0 < β t 2 :=
    zero_lt_one.trans_le (hcore t ht).2.1
  have hreg (t : ℝ) (ht : t ∈ Icc 0 (τ y)) := coreRegion_clock_regular hk (hcore t ht)
  have hF (t : ℝ) (ht : t ∈ Icc 0 (τ y)) := contDiffAt_pi.mp
    (contDiffAt_projectiveCoreLogRates hD (hdom ht) (hA t ht)
      (hV t ht) (ne_of_gt (hreg t ht).1) (ne_of_gt (hreg t ht).2.1)) i
  have H := fderiv_moving_intervalIntegral hτ hpos hF w
  have hlog : (fun x => Real.log (partialCoreReturnMultiplier τ x i)) =
      (fun x => ∫ t in 0..τ x, coreOriginalLogRates (projectiveOriginalFlow x 0 t) i) := by
    ext x
    exact log_coreFlowMultiplier _ _ _ _ _
  rw [hlog, H]
  have hparam : (∫ t in 0..τ y, fderiv ℝ (fun p : ProjectiveState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow p.1 0 p.2) i) (y, t) (w, 0)) =
      ∫ t in 0..τ y, (fderiv ℝ coreOriginalLogRates (β t) (projectiveFlowDifferential y 0 t w)) i := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc 0 (τ y) := uIcc_of_le hpos ▸ ht
    exact projectiveCoreLogRate_parameter_derivative hD (hdom ht') (hA t ht')
      (hV t ht') (ne_of_gt (hreg t ht').1) (ne_of_gt (hreg t ht').2.1) w i
  rw [hparam, coreFlow_log_rate_integral_variation hk hpos hD hdom hA hcore w i]
  have hend : τ y ∈ Icc 0 (τ y) := ⟨hpos, le_rfl⟩
  rw [partialCoreReturn_angle_derivative hD (hτ.differentiableAt (by norm_num))
    (hdom hend) (hA _ hend) (hV _ hend) w]
  dsimp only [coreLogBoundary, coreOriginalLogRates]
  simp only [projectiveOriginalFlow_initial hD, projectiveFlowDifferential_initial hD,
    ContinuousLinearMap.id_apply]
  dsimp only [L, β]
  simp only [Pi.smul_apply, smul_eq_mul, projectiveOriginalFlow_initial hD]
  ring
