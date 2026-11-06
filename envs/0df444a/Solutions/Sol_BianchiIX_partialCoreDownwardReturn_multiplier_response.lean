-- Prove2me | solution 1 for BianchiIX.partialCoreDownwardReturn_multiplier_response
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:36:09.914084+00:00
-- url     : https://prove2.me/submissions/16e05802-d3c4-40ed-a0a8-57bd7ad7aaf7

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Theorems.Thm_BianchiIX_contDiffAt_coreOriginalLogRates
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_moving_intervalIntegral_of_contDiffAt
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreClockProjection_growth
import Theorems.Thm_BianchiIX_eventually_partialCore_multiplier_formula
import Theorems.Thm_BianchiIX_exists_normalized_partialCore_return
import Theorems.Thm_BianchiIX_exists_partialCore_downward_radius_response
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_core_residence
import Theorems.Thm_BianchiIX_normalized_core_return_downward
import Theorems.Thm_BianchiIX_normalized_core_return_isLeast
import Theorems.Thm_BianchiIX_normalized_partialCore_energy_band_improves
import Theorems.Thm_BianchiIX_partialCoreReturn_log_derivative_bounds
import Theorems.Thm_BianchiIX_partialCore_field_bounds
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

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

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

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

private theorem BianchiIX.exists_normalized_partialCore_firstReturn {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    coreRadius (β s 0) (β s 2) = k → (1 < β s 2 ∨ (β s 2 = 1 ∧ 1 ≤ β s 0)) →
    (0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k) →
    (0 ≤ β s 2 * β s 3 ∧ β s 2 * β s 3 ≤ (1 / 10000) / k) →
    ∃ t > s, IsLeast {u | s < u ∧ β u 2 = 1} t ∧
      β t 0 < 1 ∧ 0 < coreAngle (β t 0) (β t 2) ∧
      deriv (fun u => β u 2) t ≤ -(1 + normalizedMaxCurve x t₀ t 0) * k / 2 ∧
      t - s ≤ 2 * k * Real.log (4 * k) ∧ ∀ u ∈ Icc s t,
        3 / (2 * k ^ 2) ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u) ∧
        |coreRadius (β u 0) (β u 2) - k| ≤ 16 * (β s 1 + (β s 2 * β s 3) ^ 2 / k) ∧
        |coreRadius (β u 0) (β u 2) ^ 2 - k ^ 2| < 1 / 16 := by
  intro β hR hVcase hU hP
  obtain ⟨t, hst, hvt, H⟩ := exists_normalized_partialCore_return hc hk hs hA hR hVcase hU hP
  have hk0 : 0 < k := by linarith only [hk]
  have hpos (u : ℝ) (hu : u ∈ Icc s t) : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) (H u hu).1
  have hr (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_radius_bounds hk (H u hu).2
  have hv (u : ℝ) (hu : u ∈ Icc s t) : 1 ≤ β u 2 := (H u hu).2.2.1
  have hwall (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_wall_bounds (H u hu).2
  have hleast := normalized_core_return_isLeast hc hk hs hst hpos
    (fun u hu => (hr u hu).1) hv (fun u hu => (hwall u hu).1) (fun u hu => (hwall u hu).2) hvt
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have hdown := normalized_core_return_downward hc hk hs hst (hpos t htm) hvt
    (fun u hu => hv u ⟨hu.1.le, hu.2.le⟩) (hr t htm).1 (hwall t htm).1 (hwall t htm).2
  have htime := (normalized_core_residence hc hk hs hst.le hpos hr hv
    (fun u hu => (hwall u hu).1) (fun u hu => (hwall u hu).2)).2
  refine ⟨t, hst, hleast, hdown.1, hdown.2.1, hdown.2.2.1, htime, ?_⟩
  intro u hu
  have hsub : Icc s u ⊆ Icc s t := fun v hv => ⟨hv.1, hv.2.trans hu.2⟩
  have Henergy := normalized_partialCore_energy_band_improves hc hk hs hu.1
    (fun v hv => hpos v (hsub hv)) hR
    (fun v hv => by rw [coreRadius_sq]; exact (H v (hsub hv)).2.1)
    (fun v hv' => hv v (hsub hv')) (fun v hv => (H v (hsub hv)).2.2.2.1)
    (fun v hv => (H v (hsub hv)).2.2.2.2)
  exact ⟨(H u hu).1, (H u hu).2, Henergy⟩

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
open Set Filter
open scoped Topology

private theorem BianchiIX.scaleCoreVariationLinear_apply (k : ℝ) (v : CoreAngleState) :
    scaleCoreVariationLinear k v = scaleCoreVariation k v := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.coreFlowMultiplier_pos (y : ProjectiveState) (t₀ a b : ℝ) (i : Fin 2) :
    0 < coreFlowMultiplier y t₀ a b i := Real.exp_pos _

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

private theorem BianchiIX.partialCore_weighted_field_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k) :
    ‖scaleCoreVariation k (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ ≤
      4 * (k ^ 2 * y 1 + (y 2 * y 3) / k) := by
  let F := coreAngleField (projectiveCoreAngle y) (toCoreAngleState y)
  let p := y 2 * y 3
  have hk0 : 0 < k := by linarith only [hk]
  have hu : 0 ≤ y 1 := hy.2.2.1.1
  have hp : 0 ≤ p := hy.2.2.2.1
  have hp1 : p ≤ 1 := (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)
  have hp2 : p ^ 2 / k ≤ p / k := div_le_div_of_nonneg_right (by nlinarith only [hp, hp1]) hk0.le
  have hku : k * y 1 ≤ k ^ 2 * y 1 := by
    have H : k ≤ k ^ 2 := by nlinarith only [hk]
    exact mul_le_mul_of_nonneg_right H hu
  obtain ⟨hR', hU, hP⟩ := partialCore_field_bounds hk hy hR
  change |F 0| ≤ 2 * (k * y 1 + p ^ 2 / k) at hR'
  change |F 1| ≤ 2 * k * y 1 at hU
  change |F 2| ≤ 4 * p / k at hP
  rw [show 4 * p / k = 4 * (p / k) by ring] at hP
  have hpdiv : 0 ≤ p / k := div_nonneg hp hk0.le
  have hkusq : 0 ≤ k ^ 2 * y 1 := mul_nonneg (sq_nonneg _) hu
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  fin_cases i
  · change |F 0| ≤ _
    linarith only [hR', hp2, hku, hkusq, hpdiv]
  · change |k * F 1| ≤ _
    rw [abs_mul, abs_of_pos hk0]
    nlinarith only [mul_le_mul_of_nonneg_left hU hk0.le, hkusq, hpdiv]
  · change |F 2| ≤ _
    linarith only [hP, hkusq]

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

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_log_partialCoreReturnMultiplier {k : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContDiffAt ℝ 1 τ y) (hpos : 0 ≤ τ y)
    (hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t))
    (i : Fin 2) : ContDiffAt ℝ 1 (fun z => Real.log (partialCoreReturnMultiplier τ z i)) y := by
  have hF (t : ℝ) (ht : t ∈ Icc 0 (τ y)) := contDiffAt_pi.mp
    (contDiffAt_projectiveCoreLogRates hD (hdom ht) (hA t ht)
      (zero_lt_one.trans_le (hcore t ht).2.1)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).1)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).2.1)) i
  convert! contDiffAt_moving_intervalIntegral_of_contDiffAt hτ hpos hF using 1
  ext z
  exact log_coreFlowMultiplier _ _ _ _ _

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_partialCoreReturnMultiplier {k : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContDiffAt ℝ 1 τ y) (hpos : 0 ≤ τ y)
    (hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t))
    (i : Fin 2) : ContDiffAt ℝ 1 (fun z => partialCoreReturnMultiplier τ z i) y := by
  convert! (contDiffAt_log_partialCoreReturnMultiplier hk hD hτ hpos hdom hA hcore i).exp using 1
  ext z
  exact (Real.exp_log (coreFlowMultiplier_pos _ _ _ _ i)).symm

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_moving_start_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (v : CoreAngleState) (dz : ℝ) :
    ‖scaleCoreVariation k
      (v - dz • coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ ≤
      4 * partialCoreVariationBudget k (y 1) (y 2 * y 3) v dz := by
  have hk0 : 0 < k := by linarith only [hk]
  let N := |v 0| + k * |v 1| + |v 2|
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hv : ‖scaleCoreVariation k v‖ ≤ N := by
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    fin_cases i
    · change |v 0| ≤ N
      dsimp [N]
      linarith only [mul_nonneg hk0.le (abs_nonneg (v 1)), abs_nonneg (v 2)]
    · change |k * v 1| ≤ N
      rw [abs_mul, abs_of_pos hk0]
      dsimp [N]
      linarith only [abs_nonneg (v 0), abs_nonneg (v 2)]
    · change |v 2| ≤ N
      dsimp [N]
      linarith only [abs_nonneg (v 0), mul_nonneg hk0.le (abs_nonneg (v 1))]
  have hfield := partialCore_weighted_field_bound hk hy hR
  rw [← scaleCoreVariationLinear_apply, map_sub, map_smul]
  calc
    _ ≤ ‖scaleCoreVariationLinear k v‖ +
        ‖dz • scaleCoreVariationLinear k
          (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ := norm_sub_le _ _
    _ = ‖scaleCoreVariation k v‖ + |dz| *
        ‖scaleCoreVariation k (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ := by
      rw [norm_smul, Real.norm_eq_abs, scaleCoreVariationLinear_apply, scaleCoreVariationLinear_apply]
    _ ≤ N + |dz| * (4 * (k ^ 2 * y 1 + (y 2 * y 3) / k)) :=
      add_le_add hv (mul_le_mul_of_nonneg_left hfield (abs_nonneg _))
    _ ≤ _ := by unfold partialCoreVariationBudget; dsimp [N] at hN ⊢; nlinarith only [hN]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_clockProjection_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (w : ProjectiveState) :
    ‖scaleCoreVariation k (coreClockProjection y w)‖ ≤
      4 * partialCoreVariationBudget k (y 1) (y 2 * y 3)
        (fderiv ℝ toCoreAngleState y w) (fderiv ℝ projectiveCoreAngle y w) :=
  partialCore_moving_start_bound hk hy hR _ _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_moving_variation_growth {beta v : ℝ → ProjectiveState} {k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b)
    (hbeta : ∀ t ∈ Icc a b, HasDerivAt beta (projectiveOriginalField (beta t)) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (fderiv ℝ projectiveOriginalField (beta t) (v t)) t)
    (hregion : ∀ t ∈ Icc a b, coreRegion k (beta t))
    (hR : coreRadius (beta a 0) (beta a 2) = k) :
    ‖scaleCoreVariation k (coreClockProjection (beta b) (v b))‖ ≤
      4 * coreVariationBound * partialCoreVariationBudget k (beta a 1) (beta a 2 * beta a 3)
        (fderiv ℝ toCoreAngleState (beta a) (v a))
        (fderiv ℝ projectiveCoreAngle (beta a) (v a)) := by
  have H := coreClockProjection_growth hk hab hbeta hv hregion
  have H0 := partialCore_clockProjection_bound hk (hregion a ⟨le_rfl, hab⟩) hR (v a)
  have hC : 0 ≤ coreVariationBound := (Real.exp_pos _).le
  exact H.trans ((mul_le_mul_of_nonneg_right H0 hC).trans_eq (by ring))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_projectedFlowVariation_bound {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdomain : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hregion : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (hR : coreRadius (projectiveOriginalFlow y t₀ a 0) (projectiveOriginalFlow y t₀ a 2) = k)
    (w : ProjectiveState) :
    let beta := projectiveOriginalFlow y t₀
    let v := projectiveFlowDifferential y t₀ a w
    ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ b w)‖ ≤
      4 * coreVariationBound * partialCoreVariationBudget k (beta a 1) (beta a 2 * beta a 3)
        (fderiv ℝ toCoreAngleState (beta a) v) (fderiv ℝ projectiveCoreAngle (beta a) v) := by
  exact partialCore_moving_variation_growth (beta := projectiveOriginalFlow y t₀)
    (v := fun t => projectiveFlowDifferential y t₀ t w) hk hab
    (fun t ht => hasDerivAt_projectiveOriginalFlow_time hD (hdomain ht) (hA t ht))
    (fun t ht => hasDerivAt_projectiveFlowDifferential_apply hD (hdomain ht) (hA t ht) w)
    hregion hR

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreDownwardReturnTime_eq {y : ProjectiveState} {T : ℝ}
    (hT : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0} T) :
    partialCoreDownwardReturnTime y = T := hT.csInf_eq

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreDownwardReturnTime_eventuallyEq {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hτ : ∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
      projectiveOriginalFlow z 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0} (τ z)) :
    partialCoreDownwardReturnTime =ᶠ[𝓝 y] τ := hτ.mono fun _ h => partialCoreDownwardReturnTime_eq h

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreDownwardReturn_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} (partialCoreDownwardReturnTime y) ∧
      ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧ ContDiffAt ℝ 2 partialCoreDownwardReturnState y ∧
      (∀ᶠ z in 𝓝 y,
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
          projectiveOriginalFlow z 0 t 2 = 1 ∧
          normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
            (partialCoreDownwardReturnTime z) ∧
        ∀ t ∈ Icc 0 (partialCoreDownwardReturnTime z), t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
          0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 t 0) ∧
      ∀ w : ProjectiveState,
        let v := fderiv ℝ toCoreAngleState y w
        let dz := fderiv ℝ projectiveCoreAngle y w
        |(fderiv ℝ partialCoreDownwardReturnState y w) 0 - v 0| ≤ 4096 * coreVariationBound *
          (|v 1| + (y 1 + y 2 * y 3) * (|v 0| + |v 2|) / k +
            (k * y 1 + (y 2 * y 3) ^ 2 / k) * |dz|) := by
  obtain ⟨T, _, hfirst, τ, hτ, hcτ, hnear, hcF, Hbound⟩ :=
    exists_partialCore_downward_radius_response hk hy hR hV
  have heq := partialCoreDownwardReturnTime_eventuallyEq (hnear.mono fun _ h => h.1)
  have hstate : partialCoreDownwardReturnState =ᶠ[𝓝 y] fun z =>
      toCoreAngleState (projectiveOriginalFlow z 0 (τ z)) := by
    filter_upwards [heq] with z hz
    simp only [partialCoreDownwardReturnState, hz]
  refine ⟨?_, hcτ.congr_of_eventuallyEq heq, hcF.congr_of_eventuallyEq hstate, ?_, ?_⟩
  · rw [heq.self_of_nhds, hτ]
    exact hfirst
  · filter_upwards [hnear, heq] with z hz ht
    simpa only [ht] using hz
  · intro w
    rw [hstate.fderiv_eq]
    exact Hbound w

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCoreDownwardReturn_bounds {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    let T := partialCoreDownwardReturnTime y
    projectiveOriginalFlow y 0 T 0 < 1 ∧ T ≤ 2 * k * Real.log (4 * k) ∧
      ∀ t ∈ Icc 0 T,
        0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
        coreRegion k (projectiveOriginalFlow y 0 t) ∧
        |coreRadius (projectiveOriginalFlow y 0 t 0) (projectiveOriginalFlow y 0 t 2) - k| ≤
          16 * (y 1 + (y 2 * y 3) ^ 2 / k) ∧
        |coreRadius (projectiveOriginalFlow y 0 t 0) (projectiveOriginalFlow y 0 t 2) ^ 2 - k ^ 2| < 1 / 16 := by
  intro T
  have hk0 : 0 < k := by linarith only [hk]
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  let β := projectiveOriginalFlow y 0
  have hzero : β 0 = y := projectiveOriginalFlow_initial hD 0
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hR0 : coreRadius (β 0 0) (β 0 2) = k := by rw [hzero]; exact hR
  have hV0 : 1 < β 0 2 ∨ (β 0 2 = 1 ∧ 1 ≤ β 0 0) := by rw [hzero]; exact hV
  have hU0 : 0 ≤ β 0 1 ∧ β 0 1 ≤ (1 / 10000) / k := by rw [hzero]; exact hy.2.2.1
  have hP0 : 0 ≤ β 0 2 * β 0 3 ∧ β 0 2 * β 0 3 ≤ (1 / 10000) / k := by
    rw [hzero]; exact hy.2.2.2
  obtain ⟨S, _, hfirstS, hM, _, _, htime, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk le_rfl hA hR0 hV0 hU0 hP0
  have hST : S = T := hfirstS.unique (partialCoreDownwardReturn_regular hk hy hR hV).1
  rw [hST] at hM htime H
  refine ⟨hM, by simpa only [sub_zero] using htime, ?_⟩
  intro t ht
  have Ht := H t ht
  change _ ∧ _ ∧ |coreRadius (β t 0) (β t 2) - k| ≤
    16 * (β 0 1 + (β 0 2 * β 0 3) ^ 2 / k) ∧ _ at Ht
  rw [hzero] at Ht
  exact ⟨lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) Ht.1, Ht.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCoreDownwardReturn_variation {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    ∀ t ∈ Icc 0 (partialCoreDownwardReturnTime y), ∀ w : ProjectiveState,
      ‖scaleCoreVariation k (coreProjectedFlowVariation y 0 t w)‖ ≤
        4 * coreVariationBound * partialCoreVariationBudget k (y 1) (y 2 * y 3)
          (fderiv ℝ toCoreAngleState y w) (fderiv ℝ projectiveCoreAngle y w) := by
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  have H := (partialCoreDownwardReturn_bounds hk hy hR hV).2.2
  have hR0 : coreRadius (projectiveOriginalFlow y 0 0 0) (projectiveOriginalFlow y 0 0 2) = k := by
    rw [projectiveOriginalFlow_initial hD]; exact hR
  intro t ht w
  have hsub : Icc 0 t ⊆ Icc 0 (partialCoreDownwardReturnTime y) := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have Hg := partialCore_projectedFlowVariation_bound hk ht.1 hD
    (fun s hs => normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.1)
    (fun s hs => (H s (hsub hs)).1) (fun s hs => (H s (hsub hs)).2.1) hR0 w
  dsimp only at Hg
  rw [projectiveOriginalFlow_initial hD, projectiveFlowDifferential_initial hD,
    ContinuousLinearMap.id_apply] at Hg
  exact Hg

end
end


/-- The fixed downward return has positive C1 multipliers with the bounds (E.23), also at V = 1. -/
theorem solution {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    let τ := partialCoreDownwardReturnTime
    (∀ᶠ x in 𝓝 y,
      projectiveOriginalFlow x 0 (τ x) 1 = x 1 * partialCoreReturnMultiplier τ x 0 ∧
      projectiveOriginalFlow x 0 (τ x) 3 = (x 2 * x 3) * partialCoreReturnMultiplier τ x 1) ∧
    (∀ i : Fin 2, 0 < partialCoreReturnMultiplier τ y i ∧
      ContDiffAt ℝ 1 (fun x => Real.log (partialCoreReturnMultiplier τ x i)) y ∧
      ContDiffAt ℝ 1 (fun x => partialCoreReturnMultiplier τ x i) y) ∧
    ∀ w : ProjectiveState,
      let dz := fderiv ℝ projectiveCoreAngle y w
      let Q₀ := partialCoreVariationBudget k (y 1) (y 2 * y 3)
        (fderiv ℝ toCoreAngleState y w) dz
      |fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x 0)) y w| ≤
        40 * coreVariationBound * Real.log (4 * k) * Q₀ + 2 * k * |dz| ∧
      |fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x 1)) y w| ≤
        236 * coreVariationBound * Real.log (4 * k) * Q₀ / k ^ 2 + 4 * |dz| / k := by
  intro τ
  have hD := (coreRegion_clock_regular hk hy).1
  have HR := partialCoreDownwardReturn_regular hk hy hR hV
  have HB := partialCoreDownwardReturn_bounds hk hy hR hV
  have hnorm := partialCoreDownwardReturn_variation hk hy hR hV
  have hpos : 0 < τ y := HR.1.1.1
  have hcτ : ContDiffAt ℝ 1 τ y := HR.2.1.of_le (by norm_num)
  have hnear := HR.2.2.2.1
  have hbase := hnear.self_of_nhds
  have hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0 :=
    fun t ht => (hbase.2 t ht).1
  have hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 :=
    fun t ht => (hbase.2 t ht).2
  have hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t) :=
    fun t ht => (HB.2.2 t ht).2.1
  have hhit : ∀ᶠ x in 𝓝 y, projectiveOriginalFlow x 0 (τ x) 2 = 1 :=
    hnear.mono fun _ h => h.1.1.2.2.1
  have hformula := eventually_partialCore_multiplier_formula hk hD hcτ.continuousAt hpos
    (hnear.mono fun _ h => h.2) hcore hhit
  refine ⟨hformula, ?_, ?_⟩
  · intro i
    exact ⟨coreFlowMultiplier_pos _ _ _ _ i,
      contDiffAt_log_partialCoreReturnMultiplier hk hD hcτ hpos.le hdom hA hcore i,
      contDiffAt_partialCoreReturnMultiplier hk hD hcτ hpos.le hdom hA hcore i⟩
  · intro w dz Q₀
    have H := partialCoreReturn_log_derivative_bounds hk hD hcτ hpos.le hdom hA hcore hhit HB.1 w
      (fun t ht => hnorm t ht w)
    exact ⟨H.1.trans_eq (by ring), H.2.trans_eq (by ring)⟩
