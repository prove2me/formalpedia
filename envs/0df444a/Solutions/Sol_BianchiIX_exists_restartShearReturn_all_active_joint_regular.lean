-- Prove2me | solution 1 for BianchiIX.exists_restartShearReturn_all_active_joint_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:50:56.360653+00:00
-- url     : https://prove2.me/submissions/7d7ae122-2b75-4717-a81f-6c1e7c57d42d

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Definitions.Def_BianchiIX_ShearTransportData
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_exists_normalized_partialCore_return
import Theorems.Thm_BianchiIX_exists_partialCore_downward_radius_response
import Theorems.Thm_BianchiIX_exists_restartShearEntrance_connection
import Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_core_residence
import Theorems.Thm_BianchiIX_normalized_core_return_downward
import Theorems.Thm_BianchiIX_normalized_core_return_isLeast
import Theorems.Thm_BianchiIX_normalized_partialCore_energy_band_improves
import Theorems.Thm_BianchiIX_partialCoreDownwardReturn_connection_domain
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
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restart_core_budget {h M q P ε : ℝ} (hq : 3 < q) (hP : 4 < P) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, 1024 * h * r ^ (q - 3) + 65536 * M * r ^ (P - 4) ≤ ε := by
  have Hq : ContinuousAt (fun r : ℝ => r ^ (q - 3)) 0 :=
    (Real.continuous_rpow_const (by linarith only [hq] : 0 ≤ q - 3)).continuousAt
  have HP : ContinuousAt (fun r : ℝ => r ^ (P - 4)) 0 :=
    (Real.continuous_rpow_const (by linarith only [hP] : 0 ≤ P - 4)).continuousAt
  have H : ContinuousAt (fun r : ℝ => 1024 * h * r ^ (q - 3) + 65536 * M * r ^ (P - 4)) 0 :=
    (continuousAt_const.mul Hq).add (continuousAt_const.mul HP)
  have Hzero : 1024 * h * (0 : ℝ) ^ (q - 3) + 65536 * M * (0 : ℝ) ^ (P - 4) < ε := by
    simpa only [Real.zero_rpow (by linarith only [hq] : q - 3 ≠ 0),
      Real.zero_rpow (by linarith only [hP] : P - 4 ≠ 0), mul_zero, add_zero] using hε
  exact ((H.eventually (isOpen_Iio.mem_nhds Hzero)).filter_mono nhdsWithin_le_nhds).mono
    (fun _ hr => hr.le)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restart_core_amplitude_budget {r h M q P ζ k u p ε : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hk : 0 < k) (hkr : k ≤ 32 / r)
    (hu : 0 ≤ u ∧ u ≤ 32 * h * r ^ (q - 2))
    (hp : 0 ≤ p ∧ p ≤ 2048 * M * ζ / r ^ 3) (hζ : ζ ≤ r ^ P)
    (hbudget : 1024 * h * r ^ (q - 3) + 65536 * M * r ^ (P - 4) ≤ ε) :
    u + p ≤ ε / k := by
  have Hsum : u + p ≤ 32 * h * r ^ (q - 2) + 2048 * M * r ^ P / r ^ 3 :=
    add_le_add hu.2 (hp.2.trans (by gcongr))
  have H := mul_le_mul hkr Hsum (add_nonneg hu.1 hp.1) (by positivity : 0 ≤ 32 / r)
  have Hq : r ^ (q - 3) = r ^ (q - 2) / r := by
    rw [show q - 3 = (q - 2) - 1 by ring, Real.rpow_sub hr, Real.rpow_one]
  have HP : r ^ (P - 4) = r ^ P / r ^ 4 := by
    simpa using Real.rpow_sub hr P (4 : ℕ)
  have Heq : 32 / r * (32 * h * r ^ (q - 2) + 2048 * M * r ^ P / r ^ 3) =
      1024 * h * r ^ (q - 3) + 65536 * M * r ^ (P - 4) := by
    rw [Hq, HP]
    field_simp
    ring
  apply (le_div_iff₀ hk).mpr
  have H' : k * (u + p) ≤ ε := ((H.trans_eq Heq).trans hbudget)
  simpa only [mul_comm k] using H'

end
end

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

private theorem BianchiIX.coreRadius_component_bounds (m v : ℝ) :
    |m - 1| ≤ coreRadius m v ∧ |v| ≤ coreRadius m v := by
  have hr : 0 ≤ coreRadius m v := Real.sqrt_nonneg _
  have he := coreRadius_sq m v
  unfold coreEnergy at he
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg v]
  · apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (m - 1)]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompact_box_bounds {x : RestartState} (hx : ‖x‖ ≤ 1 / 16) :
    |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 ∧
      246 / 256 ≤ restartRadicand x ∧ restartRadicand x ≤ 265 / 256 ∧
      15 / 16 ≤ restartCompactRoot x ∧ restartCompactRoot x ≤ 17 / 16 ∧
      -4 < restartCompactField x 0 ∧ restartCompactField x 0 < -2 := by
  have hc (i : Fin 4) : |x i| ≤ 1 / 16 := (norm_le_pi_norm x i).trans hx
  have hs (i : Fin 4) : (x i) ^ 2 ≤ 1 / 256 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hc i)
    nlinarith only [hl, hu]
  have hm (i j : Fin 4) : |x i * x j| ≤ 1 / 256 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 16 : ℝ) * (1 / 16) := mul_le_mul (hc i) (hc j) (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hQ : |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 := by
    obtain ⟨h02l, h02u⟩ := abs_le.mp (hm 0 2)
    obtain ⟨h23l, h23u⟩ := abs_le.mp (hm 2 3)
    obtain ⟨h30l, h30u⟩ := abs_le.mp (hm 3 0)
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3), h02u, h23u, h30u]
    · nlinarith only [hs 0, hs 2, hs 3, h02l, h23l, h30l]
  have hRl : 246 / 256 ≤ restartRadicand x := by
    dsimp only [restartRadicand]
    linarith only [hs 1, (abs_le.mp hQ).2]
  have hRu : restartRadicand x ≤ 265 / 256 := by
    dsimp only [restartRadicand]
    linarith only [sq_nonneg (x 1), (abs_le.mp hQ).1]
  have hr0 : 0 ≤ restartCompactRoot x := Real.sqrt_nonneg _
  have hr2 : restartCompactRoot x ^ 2 = restartRadicand x := Real.sq_sqrt (by linarith only [hRl])
  have hrl : 15 / 16 ≤ restartCompactRoot x := by nlinarith only [hr0, hr2, hRl]
  have hru : restartCompactRoot x ≤ 17 / 16 := by nlinarith only [hr0, hr2, hRu]
  refine ⟨hQ, hRl, hRu, hrl, hru, ?_, ?_⟩
  · change -4 < curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x
    linarith only [(abs_le.mp hQ).1, hru]
  · change curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x < -2
    linarith only [(abs_le.mp hQ).2, hrl]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.fromCoreAngleState_toCoreAngleState {y : ProjectiveState} (hv : 0 < y 2) :
    fromCoreAngleState (coreAngle (y 0) (y 2)) (toCoreAngleState y) = y := by
  ext i
  fin_cases i
  · exact (coreAngle_coordinates hv).2
  · rfl
  · exact (coreAngle_coordinates hv).1
  · change y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) = y 3
    rw [(coreAngle_coordinates hv).1]
    field_simp

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

private theorem BianchiIX.restartSectionChart_constraint {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 ≤ restartSectionRadicand h Z) : stateConstraint (restartSectionChart h Z) = 1 := by
  have H := Real.sq_sqrt hZ
  dsimp [stateConstraint, constraint, shearSq, restartSectionChart]
  rw [neg_sq, H]
  unfold restartSectionRadicand
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartCenterProjection_section (h : ℝ) (Z : RestartCenterState) :
    restartCenterProjection (restartSectionChart h Z) = Z := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartPhysicalCoordinates_norm_le {x : NormalizedState} {R : ℝ} (hR : 0 ≤ R)
    (hn : |x 2| ≤ R) (hZ : ‖restartCenterProjection x‖ ≤ R) :
    ‖restartPhysicalCoordinates x‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i
  · exact hn
  · exact (norm_le_pi_norm (restartCenterProjection x) 0).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 1).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 2).trans hZ

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

private theorem BianchiIX.coreAngle_abs_le_arcosh {m v : ℝ} (hv : 1 ≤ v) :
    |coreAngle m v| ≤ Real.arcosh (coreRadius m v) := by
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hk0 := coreRadius_pos (m := m) hv0
  have Hcosh : Real.cosh (coreAngle m v) ≤ coreRadius m v := by
    rw [cosh_coreAngle hv0]
    exact div_le_self hk0.le hv
  have H := (Real.arcosh_le_arcosh (Real.cosh_pos _) hk0).mpr Hcosh
  rw [← Real.cosh_abs (coreAngle m v), Real.arcosh_cosh (abs_nonneg _)] at H
  exact H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.partialCoreEntry_region {y : ProjectiveState} {ε : ℝ}
    (hk : 6 ≤ coreRadius (y 0) (y 2)) (hv : 1 ≤ y 2)
    (hu : 0 ≤ y 1) (hp : 0 ≤ y 2 * y 3)
    (hε : ε ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ ε / coreRadius (y 0) (y 2)) :
    coreRegion (coreRadius (y 0) (y 2)) y := by
  have hk0 : 0 < coreRadius (y 0) (y 2) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk
  have Hcap := hsmall.trans (div_le_div_of_nonneg_right hε hk0.le)
  refine ⟨?_, hv, ⟨hu, ?_⟩, ⟨hp, ?_⟩⟩
  · rw [coreRadius_sq, sub_self, abs_zero]
    norm_num
  · linarith only [Hcap, hp]
  · linarith only [Hcap, hu]

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
open Set

private theorem BianchiIX.restartSectionRadicand_pos_of_small {h : ℝ} {Z : RestartCenterState}
    (hh : |h| ≤ 1 / 16) (hZ : ‖Z‖ ≤ 1 / 16) : 0 < restartSectionRadicand h Z := by
  have hw := restartPhysicalCoordinates_norm_le (x := restartSectionChart h Z) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    hh (by rwa [restartCenterProjection_section])
  have H := (restartCompact_box_bounds hw).2.1
  change 246 / 256 ≤ restartSectionRadicand h Z at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionChart {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (restartSectionChart h) Z := by
  have hr : ContDiff ℝ k (restartSectionRadicand h) := by
    unfold restartSectionRadicand curvature
    fun_prop
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (hr.contDiffAt.sqrt hZ.ne').neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) Z
  · exact contDiffAt_const
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 3) Z
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 3) Z

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

private theorem BianchiIX.contDiffAt_connectionReturnPhysicalState {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    ContDiffAt ℝ 2 connectionReturnPhysicalState p := by
  have hstate := (connectionReturn_regular hμ hu hw).2.2.1
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · have hm := contDiffAt_pi.mp hstate 0
    exact ((((hm.neg.sub contDiffAt_const).pow 2).add contDiffAt_const).sqrt (by positivity))
  · exact contDiffAt_pi.mp hstate 1
  · exact contDiffAt_pi.mp hstate 2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_coreExitConnectionParameters (n : WithTop ℕ∞) {Z : CoreAngleState} (hK : 1 < Z 0) :
    ContDiffAt ℝ n coreExitConnectionParameters Z := by
  have hs : Z 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hK] : 0 < Z 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreExitConnectionParameters] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_of_constraint {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartProjectionHeight (x 2, ![x 1, x 3, x 4]) = 1 + x 0 := by
  have hd : restartProjectionDefect (x 2, ![x 1, x 3, x 4]) = 1 - (x 0) ^ 2 := by
    change (x 1) ^ 2 + curvature (x 2) (x 3) (x 4) = _
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  have hden : 1 - x 0 ≠ 0 := by linarith only [hp]
  rw [restartProjectionHeight, hd, show 1 - (1 - (x 0) ^ 2) = (x 0) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_neg hp]
  change (1 - x 0 ^ 2) / (1 - x 0) = 1 + x 0
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartProjectionDefect {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t : ℝ} (H : HasDerivAt p v t) :
    HasDerivAt (fun x => restartProjectionDefect (p x))
      (restartProjectionDefectTangent (p t) v) t := by
  have Hn : HasDerivAt (fun x => (p x).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have Hc (i : Fin 3) : HasDerivAt (fun x => (p x).2 i) (v.2 i) t := by
    let P : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact P.hasFDerivAt.comp_hasDerivAt t
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H)
  have HD := ((Hc 0).pow 2).add
    ((((Hn.pow 2).add ((Hc 1).pow 2)).add ((Hc 2).pow 2)).const_mul 2)
  have HD' := HD.sub (((Hn.add (Hc 1)).add (Hc 2)).pow 2)
  convert! HD' using 1
  · funext x
    dsimp [restartProjectionDefect, curvature]
    ring
  · dsimp [restartProjectionDefectTangent]
    ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionDefectTangent_bound {p v : RestartRadialState} {R D : ℝ}
    (hp : ‖p‖ ≤ R) (hv : ‖v‖ ≤ D) :
    |restartProjectionDefectTangent p v| ≤ 32 * R * D := by
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  have hD : 0 ≤ D := (norm_nonneg v).trans hv
  have pn : |p.1| ≤ R := (norm_fst_le p).trans hp
  have pc (i : Fin 3) : |p.2 i| ≤ R := (norm_le_pi_norm p.2 i).trans ((norm_snd_le p).trans hp)
  have vn : |v.1| ≤ D := (norm_fst_le v).trans hv
  have vc (i : Fin 3) : |v.2 i| ≤ D := (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hv)
  have ps : |p.1 + p.2 1 + p.2 2| ≤ 3 * R :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only [pn, pc 1, pc 2])
  have vs : |v.1 + v.2 1 + v.2 2| ≤ 3 * D :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only [vn, vc 1, vc 2])
  have Hsum : |p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2| ≤ 3 * R * D := by
    calc
      _ ≤ |p.1 * v.1| + |p.2 1 * v.2 1| + |p.2 2 * v.2 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ R * D + R * D + R * D := by
        simp only [abs_mul]
        gcongr
        · exact pc 1
        · exact vc 1
        · exact pc 2
        · exact vc 2
      _ = _ := by ring
  unfold restartProjectionDefectTangent
  calc
    _ ≤ |2 * p.2 0 * v.2 0| + |4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)| +
        |2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| := by
      have HT : |2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2) -
          2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| ≤
          |2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)| +
          |2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| := by
        simpa using (abs_sub_le (2 * p.2 0 * v.2 0 + 4 *
          (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)) 0
          (2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)))
      exact HT.trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * R * D + 4 * (3 * R * D) + 2 * (3 * R) * (3 * D) := by
      norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      gcongr
      · exact pc 0
      · exact vc 0
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_eq_sqrt {p : RestartRadialState}
    (hd : restartProjectionDefect p ≤ 1) :
    restartProjectionHeight p = 1 - Real.sqrt (1 - restartProjectionDefect p) := by
  have Hsq := Real.sq_sqrt (by linarith only [hd] : 0 ≤ 1 - restartProjectionDefect p)
  apply (div_eq_iff (by positivity : 1 + Real.sqrt (1 - restartProjectionDefect p) ≠ 0)).mpr
  nlinarith only [Hsq]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartProjectionHeight {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t : ℝ} (H : HasDerivAt p v t)
    (hd : restartProjectionDefect (p t) < 1) :
    HasDerivAt (fun x => restartProjectionHeight (p x))
      (restartProjectionDefectTangent (p t) v / (2 * Real.sqrt (1 - restartProjectionDefect (p t)))) t := by
  have HD := hasDerivAt_restartProjectionDefect H
  have HS := ((HD.const_sub 1).sqrt (by linarith only [hd] : 1 - restartProjectionDefect (p t) ≠ 0)).const_sub 1
  have Heq : (fun x => restartProjectionHeight (p x)) =ᶠ[𝓝 t]
      fun x => 1 - Real.sqrt (1 - restartProjectionDefect (p x)) := by
    filter_upwards [HD.continuousAt.eventually (isOpen_Iio.mem_nhds hd)] with x hx
    exact restartProjectionHeight_eq_sqrt hx.le
  convert! HS.congr_of_eventuallyEq Heq using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_derivative_bound {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t R D : ℝ} (H : HasDerivAt p v t)
    (hd : restartProjectionDefect (p t) ≤ 1 / 2) (hp : ‖p t‖ ≤ R) (hv : ‖v‖ ≤ D) :
    DifferentiableAt ℝ (fun x => restartProjectionHeight (p x)) t ∧
      |deriv (fun x => restartProjectionHeight (p x)) t| ≤ 32 * R * D := by
  have HD := hasDerivAt_restartProjectionHeight H (by linarith only [hd])
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv, abs_div, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt (1 - restartProjectionDefect (p t)))]
  have hsqrt : 1 / 2 ≤ Real.sqrt (1 - restartProjectionDefect (p t)) := by
    have Hsq := Real.sq_sqrt (by linarith only [hd] : 0 ≤ 1 - restartProjectionDefect (p t))
    nlinarith only [Hsq, Real.sqrt_nonneg (1 - restartProjectionDefect (p t)), hd]
  exact (div_le_self (abs_nonneg _) (by linarith only [hsqrt])).trans
    (restartProjectionDefectTangent_bound hp hv)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreDownwardConnection_regular {k Z ε : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k)
    (hz : projectiveCoreAngle y ≤ Z) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hu : 0 < y 1 ∧ y 1 ≤ ε / k) (hp : 0 < y 2 * y 3 ∧ y 2 * y 3 ≤ ε / k) :
    let p := fun x => coreExitConnectionParameters (partialCoreDownwardReturnState x)
    ContDiffAt ℝ 2 p y ∧
      ContDiffAt ℝ 2 (fun x => partialCoreDownwardReturnTime x + connectionReturnTime (p x)) y ∧
      ContDiffAt ℝ 2 (fun x => connectionReturnState (p x)) y := by
  intro p
  have HR := partialCoreDownwardReturn_regular hk hy hR hV
  obtain ⟨_, _, _, _, _, _, _, _, _, hct, hcs, _⟩ :=
    partialCoreDownwardReturn_connection_domain hk hy hR hV hZ hkZ hz hε hu hp
  have HB := (partialCoreDownwardReturn_bounds hk hy hR hV).2.2 _ ⟨HR.1.1.1.le, le_rfl⟩
  have hr := (coreRegion_radius_bounds hk HB.2.1).1
  have hf : 1 < partialCoreDownwardReturnState y 0 :=
    lt_of_lt_of_le (by linarith only [hk] : 1 < 99 / 100 * k) hr
  have hcP : ContDiffAt ℝ 2 p y := (contDiffAt_coreExitConnectionParameters 2 hf).comp y HR.2.2.1
  exact ⟨hcP, HR.2.1.add (ContDiffAt.comp (g := connectionReturnTime) (f := p) y hct hcP),
    ContDiffAt.comp (g := connectionReturnState) (f := p) y hcs hcP⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionDefect_shear_bounds {p : RestartRadialState} {a σ : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 128) (hσ : |σ| = 1)
    (hs : 3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ a ^ 2)
    (h₂ : 0 ≤ p.2 1 ∧ p.2 1 ≤ a / 16) (h₃ : 0 ≤ p.2 2 ∧ p.2 2 ≤ a / 16) :
    a ^ 2 / 2 ≤ restartProjectionDefect p ∧ restartProjectionDefect p ≤ 6 * a ^ 2 := by
  have hsig : σ ^ 2 = 1 := by nlinarith only [sq_abs σ, hσ]
  have hsq : (σ * p.2 0) ^ 2 = (p.2 0) ^ 2 := by rw [mul_pow, hsig, one_mul]
  have hslo := pow_le_pow_left₀ (by positivity [ha.1] : 0 ≤ 3 * a / 4) hs.1 2
  have hshi := pow_le_pow_left₀ (by linarith only [hs.1, ha.1] : 0 ≤ σ * p.2 0) hs.2 2
  rw [hsq] at hslo hshi
  have hsum : p.2 1 + p.2 2 ≤ a / 8 := by linarith only [h₂.2, h₃.2]
  have hcross := mul_le_mul hn.2 hsum (add_nonneg h₂.1 h₃.1) (sq_nonneg a)
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have ha3 : a ^ 2 * a ≤ a ^ 2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 (sq_nonneg a)
  have hnsq := pow_le_pow_left₀ hn.1 hn.2 2
  have hdiff : |p.2 1 - p.2 2| ≤ a / 16 :=
    abs_le.mpr ⟨by linarith only [h₂.1, h₃.2], by linarith only [h₃.1, h₂.2]⟩
  have hdsq := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  rw [sq_abs] at hdsq
  have heq : restartProjectionDefect p = (p.2 0) ^ 2 + p.1 ^ 2 + (p.2 1 - p.2 2) ^ 2 -
      2 * p.1 * (p.2 1 + p.2 2) := by unfold restartProjectionDefect curvature; ring
  constructor
  · rw [heq]
    have ha3small := mul_le_mul_of_nonneg_left ha.2 (sq_nonneg a)
    nlinarith only [hslo, hcross, ha3small, sq_nonneg p.1, sq_nonneg (p.2 1 - p.2 2), sq_nonneg a]
  · rw [heq]
    have hneg := mul_nonneg hn.1 (add_nonneg h₂.1 h₃.1)
    have hnsmall := mul_le_mul_of_nonneg_left ha.2 ha.1.le
    have hn4small := mul_le_mul_of_nonneg_left hnsmall (sq_nonneg a)
    nlinarith only [hshi, hnsq, hn4small, hdsq, hneg, ha3, sq_nonneg a]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_shear_bounds {p : RestartRadialState} {a σ : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 128) (hσ : |σ| = 1)
    (hs : 3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ a ^ 2)
    (h₂ : 0 ≤ p.2 1 ∧ p.2 1 ≤ a / 16) (h₃ : 0 ≤ p.2 2 ∧ p.2 2 ≤ a / 16) :
    restartProjectionDefect p ≤ 1 / 2 ∧
      a ^ 2 / 4 ≤ restartProjectionHeight p ∧ restartProjectionHeight p ≤ 6 * a ^ 2 := by
  obtain ⟨Hlo, Hhi⟩ := restartProjectionDefect_shear_bounds ha hσ hs hn h₂ h₃
  have hd0 : 0 ≤ restartProjectionDefect p := le_trans (by positivity) Hlo
  have hd1 : restartProjectionDefect p ≤ 1 / 2 := by nlinarith only [Hhi, ha.1, ha.2]
  have hsqrt := Real.sqrt_nonneg (1 - restartProjectionDefect p)
  have hsqrt1 : Real.sqrt (1 - restartProjectionDefect p) ≤ 1 := by rw [Real.sqrt_le_one]; linarith only [hd0]
  have hden : 0 < 1 + Real.sqrt (1 - restartProjectionDefect p) := by positivity
  refine ⟨hd1, (le_div_iff₀ hden).mpr ?_, (div_le_iff₀ hden).mpr ?_⟩
  · nlinarith only [Hlo, mul_le_mul_of_nonneg_left hsqrt1 (sq_nonneg a)]
  · nlinarith only [Hhi, mul_nonneg (sq_nonneg a) hsqrt]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartShearCurve (σ n₂ n₃ ρ : ℝ) :
    HasDerivAt (restartShearCurve σ n₂ n₃) (restartShearDirection σ) ρ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [restartShearCurve, restartShearDirection] using (hasDerivAt_id ρ).const_mul σ
  · convert! hasDerivAt_const ρ n₂ using 1
  · convert! hasDerivAt_const ρ n₃ using 1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShearCurve_annulus {a ρ σ ε n₂ n₃ : ℝ} (ha : 0 < a)
    (hρ : ρ ∈ Icc a (2 * a)) (hσ : |σ| = 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 64)
    (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) :
    ‖restartShearCurve σ n₂ n₃ ρ‖ ≤ 2 * a ∧
      a ≤ restartRadialNorm (restartShearCurve σ n₂ n₃ ρ) ∧ |n₂ - n₃| ≤ 2 * ε * a := by
  have hρpos := ha.trans_le hρ.1
  have hsmall : 2 * ε * a ≤ 2 * a := by nlinarith only [hε.2, ha]
  refine ⟨?_, ?_, abs_le.mpr ⟨by linarith only [h₂.1, h₃.2], by linarith only [h₃.1, h₂.2]⟩⟩
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * a)).mpr
    intro i
    fin_cases i
    · change |σ * ρ| ≤ 2 * a
      simpa only [abs_mul, hσ, abs_of_pos hρpos, one_mul] using hρ.2
    · exact (show |n₂| ≤ 2 * ε * a by simpa only [abs_of_nonneg h₂.1] using h₂.2).trans hsmall
    · exact (show |n₃| ≤ 2 * ε * a by simpa only [abs_of_nonneg h₃.1] using h₃.2).trans hsmall
  · have H := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg (n₂ - n₃)) :
        (σ * ρ) ^ 2 ≤ (σ * ρ) ^ 2 + (n₂ - n₃) ^ 2)
    rw [Real.sqrt_sq_eq_abs, abs_mul, hσ, abs_of_pos hρpos, one_mul] at H
    exact hρ.1.trans H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restartSectionProjectionHeight_eq {h T : ℝ} {Z : RestartCenterState}
    (hrad : 0 < restartSectionRadicand h Z) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h Z) 0 T 0 < 0) :
    (fun W => restartProjectionHeight (restartSectionRadialState h T W)) =ᶠ[𝓝 Z]
      (fun W => 1 + normalizedMaxCurve (restartSectionChart h W) 0 T 0) := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have Hchart := (contDiffAt_restartSectionChart hrad 1).continuousAt
  have Hflow := (hasFDerivAt_normalizedMaxCurve_initial hdom).continuousAt.comp Hchart
  have Hcoord : ContinuousAt (fun W => normalizedMaxCurve (restartSectionChart h W) 0 T 0) Z :=
    (continuous_apply 0).continuousAt.comp Hflow
  have HR : ContinuousAt (restartSectionRadicand h) Z := by
    unfold restartSectionRadicand curvature
    fun_prop
  filter_upwards [HR.eventually (isOpen_Ioi.mem_nhds hrad),
    Hcoord.eventually (isOpen_Iio.mem_nhds hneg)] with W hW hN
  have HC := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hW.le) hT).2.1
  exact restartProjectionHeight_of_constraint HC hN

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartFastShearProjectiveEntry_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q : ℝ, 2 < q →
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε σ n₂ n₃ : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let T := q / 2 * Real.log (1 / a)
          let y := restartFastShearProjectiveEntry h T σ n₂ n₃ ρ
          T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
          DifferentiableAt ℝ (restartFastShearProjectiveEntry h T σ n₂ n₃) ρ ∧
          DifferentiableAt ℝ (restartFastShearHeight h T σ n₂ n₃) ρ ∧
          a ^ 2 / 4 ≤ restartFastShearHeight h T σ n₂ n₃ ρ ∧
          restartFastShearHeight h T σ n₂ n₃ ρ ≤ 6 * a ^ 2 ∧
          |deriv (restartFastShearHeight h T σ n₂ n₃) ρ| ≤ 512 * a ∧
          (1 / (8 * a) ≤ σ * y 0 ∧ σ * y 0 ≤ 18 / a) ∧
          (0 < y 1 ∧ y 1 ≤ 8 * h * a ^ (q - 2)) ∧
          (n₂ / (12 * a ^ 2) ≤ y 2 ∧ y 2 ≤ 16 * n₂ / a ^ 2) ∧
          (n₃ / (12 * a ^ 2) ≤ y 3 ∧ y 3 ≤ 16 * n₃ / a ^ 2) ∧
          (0 ≤ y 2 + y 3 ∧ y 2 + y 3 ≤ 64 * ε / a) ∧
          (0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 256 * n₂ * n₃ / a ^ 4) := by
  obtain ⟨C, _, h₀, hh₀, H₀⟩ := exists_restartShearFastEntry_control
  refine ⟨min h₀ 1, lt_min hh₀ (by norm_num), ?_⟩
  intro h hh q hq
  obtain ⟨astar, hastar, Ha⟩ := H₀ h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ T y
  let Z := restartShearCurve σ n₂ n₃ ρ
  let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
  let p := restartSectionRadialState h T Z
  obtain ⟨ha1, hasmall, hT, hrad, hdom, _, hneg, Hcurve, hnpos, hnexp, hshear, hc, hv, _, hw⟩ :=
    Ha a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  change 0 < x 2 at hnpos
  change x 2 ≤ h * a ^ q at hnexp
  change 3 * a / 4 ≤ σ * x 1 ∧ σ * x 1 ≤ 9 * a / 4 at hshear
  have hnsq : p.1 ≤ a ^ 2 := hnexp.trans (by
    have HP : a ^ q ≤ a ^ 2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hq.le
    exact (mul_le_mul_of_nonneg_left HP hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg a) (hh.2.trans (min_le_right _ _))))
  have Hweak (i : Fin 2) : 0 ≤ p.2 i.succ ∧ p.2 i.succ ≤ a / 16 := by
    have hZi : 0 ≤ Z i.succ ∧ Z i.succ ≤ 2 * ε * a := by fin_cases i; exact h₂; exact h₃
    constructor
    · exact (div_nonneg hZi.1 (by norm_num)).trans (hw i).1
    · have H := (hw i).2.1.trans (mul_le_mul_of_nonneg_left hZi.2 (by norm_num))
      nlinarith only [H, mul_le_mul_of_nonneg_right hε.2 ha.1.le]
  have hpsmall : ‖p‖ ≤ 8 * a := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_of_pos (show 0 < p.1 from hnpos)]
    refine ⟨hnsq.trans ?_, hc⟩
    nlinarith only [ha.1, ha1]
  obtain ⟨hd, Hlo, Hhi⟩ := restartProjectionHeight_shear_bounds
    ⟨ha.1, by linarith only [hasmall]⟩ hσ hshear ⟨hnpos.le, hnsq⟩ (Hweak 0) (Hweak 1)
  have Hgerm := (eventually_restartSectionProjectionHeight_eq hrad hT (by linarith only [hneg])).comp_tendsto
    (hasDerivAt_restartShearCurve σ n₂ n₃ ρ).continuousAt
  change (fun t => restartProjectionHeight (restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t))) =ᶠ[𝓝 ρ]
    restartFastShearHeight h T σ n₂ n₃ at Hgerm
  have HD := restartProjectionHeight_derivative_bound Hcurve hd hpsmall hv
  have Hactual := HD.1.hasDerivAt.congr_of_eventuallyEq Hgerm.symm
  change a ^ 2 / 4 ≤ restartProjectionHeight p at Hlo
  change restartProjectionHeight p ≤ 6 * a ^ 2 at Hhi
  have heq : restartProjectionHeight p = 1 + x 0 := Hgerm.eq_of_nhds
  rw [heq] at Hlo Hhi
  have hA : 0 < 1 + x 0 := (by positivity [ha.1] : 0 < a ^ 2 / 4).trans_le Hlo
  have Hchart := ((contDiffAt_restartSectionChart hrad 1).differentiableAt (by norm_num)).comp ρ
    (hasDerivAt_restartShearCurve σ n₂ n₃ ρ).differentiableAt
  have HX := (hasFDerivAt_normalizedMaxCurve_initial hdom).differentiableAt.comp ρ Hchart
  have HY := ((contDiffAt_toProjectiveState 1 hA.ne').differentiableAt (by norm_num)).comp ρ HX
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrt, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrt, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have Hcoord (u u₀ : ℝ) (hu₀ : 0 ≤ u₀) (hu : u₀ / 2 ≤ u ∧ u ≤ 2 * u₀) :
      u₀ / (12 * a ^ 2) ≤ Real.sqrt 3 * u / (1 + x 0) ∧
        Real.sqrt 3 * u / (1 + x 0) ≤ 16 * u₀ / a ^ 2 := by
    have hu0 : 0 ≤ u := (div_nonneg hu₀ (by norm_num)).trans hu.1
    constructor
    · calc
        _ = (u₀ / 2) / (6 * a ^ 2) := by ring
        _ ≤ _ := div_le_div₀ (by positivity)
          (hu.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt1 hu0])) hA Hhi
    · calc
        _ ≤ (4 * u₀) / (a ^ 2 / 4) := div_le_div₀ (by positivity)
          (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hu0, hu.2]) (by positivity [ha.1]) Hlo
        _ = _ := by ring
  have HV := Hcoord (x 3) n₂ h₂.1 ⟨(hw 0).1, (hw 0).2.1⟩
  have HW := Hcoord (x 4) n₃ h₃.1 ⟨(hw 1).1, (hw 1).2.1⟩
  have hyV : 0 ≤ y 2 := (div_nonneg h₂.1 (by positivity)).trans HV.1
  have hyW : 0 ≤ y 3 := (div_nonneg h₃.1 (by positivity)).trans HW.1
  refine ⟨hdom, HY, Hactual.differentiableAt, Hlo, Hhi, ?_, ?_, ?_, HV, HW, ?_, ?_⟩
  · rw [Hactual.deriv]
    exact HD.2.trans (by ring_nf; rfl)
  · have heqM : σ * y 0 = Real.sqrt 3 * (σ * x 1) / (1 + x 0) := by
      change σ * (Real.sqrt 3 * x 1 / (1 + x 0)) = _
      ring
    rw [heqM]
    have hspos : 0 ≤ σ * x 1 := (by positivity [ha.1] : 0 ≤ 3 * a / 4).trans hshear.1
    constructor
    · calc
        _ = (3 * a / 4) / (6 * a ^ 2) := by field_simp; ring
        _ ≤ _ := div_le_div₀ (by positivity [ha.1])
          (hshear.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt1 hspos])) hA Hhi
    · calc
        _ ≤ (2 * (9 * a / 4)) / (a ^ 2 / 4) := div_le_div₀ (by positivity [ha.1])
          (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hspos, hshear.2]) (by positivity [ha.1]) Hlo
        _ = _ := by field_simp; ring
  · refine ⟨div_pos (mul_pos hsqrt hnpos) hA, ?_⟩
    calc
      y 1 ≤ (2 * (h * a ^ q)) / (a ^ 2 / 4) := div_le_div₀ (by positivity [hh.1, ha.1])
        (by
          change Real.sqrt 3 * x 2 ≤ 2 * (h * a ^ q)
          nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hnpos.le, hnexp]) (by positivity [ha.1]) Hlo
      _ = _ := by rw [Real.rpow_sub ha.1, Real.rpow_two]; ring
  · refine ⟨add_nonneg hyV hyW, ?_⟩
    calc
      y 2 + y 3 ≤ 16 * n₂ / a ^ 2 + 16 * n₃ / a ^ 2 := add_le_add HV.2 HW.2
      _ ≤ 16 * (2 * ε * a) / a ^ 2 + 16 * (2 * ε * a) / a ^ 2 := by gcongr; exact h₂.2; exact h₃.2
      _ = _ := by field_simp; ring
  · refine ⟨mul_nonneg hyV hyW, ?_⟩
    calc
      y 2 * y 3 ≤ (16 * n₂ / a ^ 2) * (16 * n₃ / a ^ 2) :=
        mul_le_mul HV.2 HW.2 hyW (by positivity [h₂.1])
      _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.shearCore_geometry {a m v : ℝ} (ha : a ∈ Ioc (0 : ℝ) (1 / 128))
    (hm : 1 / (8 * a) ≤ m ∧ m ≤ 18 / a) (hv : 0 ≤ v ∧ v ≤ 1 / a) :
    1 < m ∧ 6 ≤ coreRadius m v ∧ 1 / (16 * a) ≤ coreRadius m v ∧
      coreRadius m v ≤ 32 / a ∧
      (1 ≤ v → coreAngle m v ∈ Icc (-Real.arcosh (coreRadius m v)) 0) := by
  have hapos := ha.1
  have hm1 : 1 < m := lt_of_lt_of_le
    ((lt_div_iff₀ (by positivity : 0 < 8 * a)).mpr (by linarith only [ha.2])) hm.1
  have hgap : 1 / (16 * a) ≤ m - 1 := by
    have H : (1 : ℝ) ≤ 1 / (16 * a) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith only [ha.2])
    have heq : 1 / (8 * a) = 2 * (1 / (16 * a)) := by ring
    rw [heq] at hm
    linarith only [hm.1, H]
  have hklo := hgap.trans ((le_abs_self _).trans (coreRadius_component_bounds m v).1)
  have hk6 : 6 ≤ coreRadius m v := le_trans
    ((le_div_iff₀ (by positivity : 0 < 16 * a)).mpr (by linarith only [ha.2])) hklo
  have hkadd : coreRadius m v ≤ m + v := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by linarith only [hm1, hv.1])).mp
    change coreRadius m v ^ 2 ≤ (m + v) ^ 2
    rw [coreRadius_sq]
    unfold coreEnergy
    nlinarith only [hm1, mul_nonneg (by linarith only [hm1] : 0 ≤ m) hv.1]
  have hkhi : coreRadius m v ≤ 32 / a := hkadd.trans (by
    have H := add_le_add hm.2 hv.2
    have H19 : (18 : ℝ) / a + 1 / a ≤ 32 / a := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) ha.1.le
    exact H.trans H19)
  refine ⟨hm1, hk6, hklo, hkhi, ?_⟩
  intro hv1
  refine ⟨(abs_le.mp (coreAngle_abs_le_arcosh hv1)).1, ?_⟩
  change Real.arsinh ((1 - m) / v) ≤ 0
  have H : (1 - m) / v ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith only [hm1]) hv.1
  simpa only [Real.arsinh_zero] using Real.arsinh_le_arsinh.mpr H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartFastShearCore_geometry :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q : ℝ, 2 < q →
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 64) → (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) →
        (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let T := q / 2 * Real.log (1 / a)
          let y := restartFastShearProjectiveEntry h T 1 n₂ n₃ ρ
          let k := restartFastShearCoreRadius h T 1 n₂ n₃ ρ
          let z := restartFastShearCoreAngle h T 1 n₂ n₃ ρ
          0 ≤ T ∧ 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
          T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
          0 < restartFastShearHeight h T 1 n₂ n₃ ρ ∧
          DifferentiableAt ℝ (restartFastShearProjectiveEntry h T 1 n₂ n₃) ρ ∧
          1 < y 0 ∧ 6 ≤ k ∧ 1 / (16 * a) ≤ k ∧ k ≤ 32 / a ∧
          (1 ≤ y 2 → z ∈ Icc (-Real.arcosh k) 0) := by
  obtain ⟨hP, hhP, HP⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hP (1 / 16), lt_min hhP (by norm_num), ?_⟩
  intro h hh q hq
  obtain ⟨aP, haP, HaP⟩ := HP h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  refine ⟨min aP (1 / 128), lt_min haP (by norm_num), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ ρ hρ T y k z
  have ha128 : a ≤ 1 / 128 := ha.2.trans (min_le_right _ _)
  obtain ⟨Hdom, HY, _, HA, _, _, HM, _, HV, HW, HS, _⟩ :=
    HaP a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε (by norm_num) h₂ h₃ ρ hρ
  change 1 / (8 * a) ≤ 1 * y 0 ∧ 1 * y 0 ≤ 18 / a at HM
  simp only [one_mul] at HM
  have hv0 : 0 ≤ y 2 := (div_nonneg h₂.1 (by positivity)).trans HV.1
  have hw0 : 0 ≤ y 3 := (div_nonneg h₃.1 (by positivity)).trans HW.1
  have hvhi : y 2 ≤ 1 / a := by
    have H : y 2 + y 3 ≤ 64 * ε / a := HS.2
    have HB : 64 * ε / a ≤ 1 / a := div_le_div_of_nonneg_right
      (by linarith only [hε.2]) ha.1.le
    linarith only [H, HB, hw0]
  have HG := shearCore_geometry ⟨ha.1, ha128⟩ HM ⟨hv0, hvhi⟩
  have hsmall : ‖restartShearCurve 1 n₂ n₃ ρ‖ ≤ 1 / 16 :=
    (restartShearCurve_annulus ha.1 hρ (by norm_num) hε h₂ h₃).1.trans
      (by linarith only [ha128])
  have hrad := restartSectionRadicand_pos_of_small
    (by rw [abs_of_pos hh.1]; exact hh.2.trans (min_le_right _ _)) hsmall
  have hT : 0 ≤ T := mul_nonneg (by linarith only [hq])
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by linarith only [ha128])))
  exact ⟨hT, hrad, Hdom, (by positivity [ha.1] : 0 < a ^ 2 / 4).trans_le HA, HY, HG⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartShearPartialCore_entry :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 64) → (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            let y := restartFastShearProjectiveEntry h T 1 n₂ n₃ ρ
            let k := restartFastShearCoreRadius h T 1 n₂ n₃ ρ
            let z := restartFastShearCoreAngle h T 1 n₂ n₃ ρ
            0 ≤ T ∧ 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
            T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
            0 < restartFastShearHeight h T 1 n₂ n₃ ρ ∧
            1 < y 0 ∧ 6 ≤ k ∧ 1 / (16 * a) ≤ k ∧ k ≤ 32 / a ∧
            toCoreAngleState y 0 = k ∧ 0 < y 1 ∧ 0 ≤ y 2 * y 3 ∧
            y 1 + y 2 * y 3 ≤ η / k ∧
            (1 ≤ y 2 → z ∈ Icc (-Real.arcosh k) 0 ∧
              fromCoreAngleState z (toCoreAngleState y) = y ∧ coreRegion k y ∧
              (1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0))) := by
  obtain ⟨hG, hhG, HG⟩ := exists_restartFastShearCore_geometry
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hG hV, lt_min hhG hhV, ?_⟩
  intro h hh q P hq hP η hη
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨aG, haG, HaG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq2
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q hq2
  obtain ⟨aB, haB, HaB⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_core_budget (h := h) (M := 1) hq hP hη.1)
  refine ⟨min aG (min aV aB), lt_min haG (lt_min haV haB), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ T y k z
  have hapos := ha.1
  obtain ⟨hT, hrad, hdom, hA, _, hm, hk, hklo, hkhi, hz⟩ :=
    HaG a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ ρ hρ
  obtain ⟨_, _, _, _, _, _, _, hu, _, _, _, hp⟩ :=
    HaV a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
      ε 1 n₂ n₃ hε (by norm_num) h₂ h₃ ρ hρ
  change 6 ≤ k at hk
  change k ≤ 32 / a at hkhi
  change 0 < y 1 ∧ y 1 ≤ 8 * h * a ^ (q - 2) at hu
  change 0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 256 * n₂ * n₃ / a ^ 4 at hp
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk
  have hn₂ : n₂ ≤ a := by
    have H := mul_le_mul_of_nonneg_right hε.2 ha.1.le
    nlinarith only [h₂.2, H, ha.1]
  have HU : 0 ≤ y 1 ∧ y 1 ≤ 32 * h * a ^ (q - 2) := ⟨hu.1.le, hu.2.trans (by
    nlinarith only [mul_nonneg hh.1.le (Real.rpow_nonneg ha.1.le (q - 2))])⟩
  have HP : 0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 2048 * 1 * n₃ / a ^ 3 := by
    refine ⟨hp.1, hp.2.trans ?_⟩
    calc
      _ ≤ 256 * a * n₃ / a ^ 4 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hn₂]) h₃.1) (by positivity)
      _ = 256 * n₃ / a ^ 3 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) h₃.1) (by positivity)
  have HB := HaB ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have Hbudget : y 1 + y 2 * y 3 ≤ η / k :=
    restart_core_amplitude_budget ha.1 (by norm_num : (0 : ℝ) ≤ 1) hk0 hkhi HU HP h₃P HB
  refine ⟨hT, hrad, hdom, hA, hm, hk, hklo, hkhi, rfl, hu.1, hp.1, Hbudget, ?_⟩
  intro hv
  refine ⟨hz hv, fromCoreAngleState_toCoreAngleState (zero_lt_one.trans_le hv),
    partialCoreEntry_region hk hv hu.1.le hp.1 hη.2 Hbudget, ?_⟩
  rcases eq_or_lt_of_le hv with heq | hlt
  · exact Or.inr ⟨heq.symm, hm.le⟩
  · exact Or.inl hlt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartFastShearProjectiveEntry_flow {h s σ n₂ n₃ ρ t : ℝ}
    (hrad : 0 ≤ restartSectionRadicand h (restartShearCurve σ n₂ n₃ ρ))
    (hs : 0 ≤ s) (hA : 0 < restartFastShearHeight h s σ n₂ n₃ ρ) (ht : 0 ≤ t) :
    projectiveOriginalFlow (restartFastShearProjectiveEntry h s σ n₂ n₃ ρ) 0 t =
      toProjectiveState (normalizedMaxCurve (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 (s + t)) := by
  have hc := restartSectionChart_constraint hrad
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hbase := fromProjectiveState_toProjectiveState hA.ne'
    ((normalizedMaxCurve_constraint hdom).trans hc)
  have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hdom)
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hs))
  simp only [zero_add] at H
  change toProjectiveState (normalizedMaxCurve
    (fromProjectiveState (toProjectiveState (normalizedMaxCurve _ 0 s))) 0 t) = _
  rw [hbase, H, add_comm t s]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearPartialCore_downward_connection :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
              let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
              let k := restartFastShearCoreRadius h s 1 n₂ n₃ ρ
              let T := partialCoreDownwardReturnTime y
              let out := projectiveOriginalFlow y 0 T
              let p := coreExitConnectionParameters (partialCoreDownwardReturnState y)
              1 ≤ y 2 →
              0 < T ∧ IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1} (s + T) ∧
              out = connectionEntry (p 0) (p 1) (p 2) ∧
              (4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k) ∧
              (0 < p 1 ∧ p 1 ≤ η / p 0) ∧ (0 < p 2 ∧ p 2 ≤ η) ∧
              p 1 ≤ y 1 * Real.exp (-k / 12) ∧ p 2 ≤ y 2 * y 3 ∧
              phaseNorm (p 0 + 1) 1 = coreRadius (out 0) (out 2) ∧
              connectionReturnValid p ∧ ContDiffAt ℝ 2 connectionReturnTime p ∧
              ContDiffAt ℝ 2 connectionReturnState p ∧
              connectionReturnState p = toProjectiveState
                (normalizedMaxCurve x 0 (s + T + connectionReturnTime p)) ∧
              let Q := fun z => coreExitConnectionParameters (partialCoreDownwardReturnState z)
              ContDiffAt ℝ 2 Q y ∧
                ContDiffAt ℝ 2 (fun z => partialCoreDownwardReturnTime z + connectionReturnTime (Q z)) y ∧
                ContDiffAt ℝ 2 (fun z => connectionReturnState (Q z)) y := by
  obtain ⟨hstar, hhstar, H⟩ := exists_restartShearPartialCore_entry
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q P hq hP η hη
  obtain ⟨astar, hastar, Ha⟩ := H h hh q P hq hP η hη
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s x y k T out p hv
  obtain ⟨hs, hrad, _, hA, _, hk, _, _, hR, hu0, hp0, hsum, Hentry⟩ :=
    Ha a ha ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ
  obtain ⟨hz, _, hy, hvcase⟩ := Hentry hv
  have hc : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have Hsign := normalizedMaxCurve_wall_sign hc hs (2 : Fin 3)
  have hnpos : 0 < normalizedMaxCurve x 0 s 4 := by
    have Hnonneg : 0 ≤ wallValue 2 (normalizedMaxCurve x 0 s) := Hsign.2.mpr h₃.1.le
    have Hne : wallValue 2 (normalizedMaxCurve x 0 s) ≠ 0 := fun hzero => h₃.1.ne' (Hsign.1.mp hzero)
    exact lt_of_le_of_ne Hnonneg (Ne.symm Hne)
  have hwpos : 0 < y 3 := div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hnpos) hA
  have hp : 0 < y 2 * y 3 := mul_pos (zero_lt_one.trans_le hv) hwpos
  have huη : y 1 ≤ η / k := (le_add_of_nonneg_right hp0).trans hsum
  have hpη : y 2 * y 3 ≤ η / k := (le_add_of_nonneg_left hu0.le).trans hsum
  have hkZ : 2 * Real.cosh 0 ≤ k := by rw [Real.cosh_zero]; linarith only [hk]
  obtain ⟨hentry, hμ, hu, hw, hdecU, hdecP, hphase, _, hvalid, hct, hcs, Hconn⟩ :=
    partialCoreDownwardReturn_connection_domain hk hy hR hvcase (le_refl (0 : ℝ)) hkZ hz.2 hη
      ⟨hu0, huη⟩ ⟨hp, hpη⟩
  have Hreg := partialCoreDownwardConnection_regular hk hy hR hvcase (le_refl (0 : ℝ)) hkZ hz.2 hη
    ⟨hu0, huη⟩ ⟨hp, hpη⟩
  have hfirst := (partialCoreDownwardReturn_regular hk hy hR hvcase).1
  have hT : 0 < T := hfirst.1.1
  have htc : 0 < connectionReturnTime p := hvalid.1.1.1
  have Hflow (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_flow hrad.le hs hA ht
  have Hfast := Hflow (T + connectionReturnTime p) (add_nonneg hT.le htc.le)
  refine ⟨hT, ?_, hentry, hμ, hu, hw, hdecU, hdecP, hphase, hvalid, hct, hcs, ?_, Hreg⟩
  · refine ⟨⟨by linarith only [hT], ?_⟩, ?_⟩
    · rw [← Hflow T hT.le]
      exact hfirst.1.2
    · intro t ht
      have hsub : 0 < t - s := sub_pos.mpr ht.1
      have HF := Hflow (t - s) hsub.le
      rw [add_sub_cancel] at HF
      have Hleast := hfirst.2 ⟨hsub, by rw [HF]; exact ht.2⟩
      linarith only [Hleast]
  · exact (Hconn.trans Hfast).trans (by rw [add_assoc])

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_restartFastShearProjectiveEntry_joint {h s σ n₂ n₃ ρ : ℝ}
    (hZ : 0 < restartSectionRadicand h (restartShearCurve σ n₂ n₃ ρ))
    (hs : s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0)
    (hA : restartFastShearHeight h s σ n₂ n₃ ρ ≠ 0) :
    ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s σ p.1.1 p.1.2 p.2)
      ((n₂, n₃), ρ) := by
  have hc : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearCurve σ p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [restartShearCurve] <;> fun_prop
  have hchart := (contDiffAt_restartSectionChart hZ 2).comp ((n₂, n₃), ρ) hc
  have hflow := (contDiffAt_normalizedMaxCurve_two hs).comp ((n₂, n₃), ρ)
    (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
    (hchart.prodMk (contDiffAt_const (c := s)))
  exact (contDiffAt_toProjectiveState 2 hA).comp ((n₂, n₃), ρ) hflow

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearReturn_joint_regular :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2 →
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s 1 p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnState h s p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnTime h s p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearPartialCore_entry
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearPartialCore_downward_connection
  refine ⟨min hE hC, lt_min hhE hhC, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min aE aC, lt_min haE haC, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s hv
  obtain ⟨_, hrad, hdom, hA, _, hk, _, _, hR, _, _, _, Hentry⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ
  obtain ⟨_, _, hy, hvcase⟩ := Hentry hv
  obtain ⟨_, _, _, hμ, hu, hw, _, _, _, _, hct, _, _, hcp, _⟩ :=
    HaC a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  let base : (ℝ × ℝ) × ℝ := ((n₂, n₃), ρ)
  let Y := fun p : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s 1 p.1.1 p.1.2 p.2
  have hcY : ContDiffAt ℝ 2 Y base := contDiffAt_restartFastShearProjectiveEntry_joint hrad hdom hA.ne'
  have Hcore := partialCoreDownwardReturn_regular hk hy hR hvcase
  have hcP : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s p.1.1 p.1.2 p.2) base :=
    ContDiffAt.comp (g := fun z => coreExitConnectionParameters (partialCoreDownwardReturnState z))
      (f := Y) base hcp hcY
  have hcG : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnState h s p.1.1 p.1.2 p.2) base :=
    ContDiffAt.comp (g := connectionReturnPhysicalState) base
      (contDiffAt_connectionReturnPhysicalState hμ.1 ⟨hu.1.le, hu.2⟩ hw) hcP
  have hg0 : restartShearReturnState h s n₂ n₃ ρ 0 ≠ 0 := by
    change phaseNorm (-connectionReturnState (restartShearReturnParameters h s n₂ n₃ ρ) 0 - 1) 1 ≠ 0
    exact ne_of_gt (by unfold phaseNorm; positivity)
  have hcphase : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s p.1.1 p.1.2 p.2) base :=
    contDiffAt_const.div (contDiffAt_pi.mp hcG 0) hg0
  have hctime : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnTime h s p.1.1 p.1.2 p.2) base :=
    (contDiffAt_const.add (Hcore.2.1.comp base hcY)).add
      (ContDiffAt.comp (g := connectionReturnTime) base hct hcP)
  exact ⟨hcY, hcP, hcG, hcphase, hctime⟩

end
end

/-- The fixed shear return is jointly C2 throughout the positive-wall annulus, without an active-wall cutoff. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) := by
  obtain ⟨hU, hhU, HU⟩ := exists_restartShearReturn_joint_regular
  obtain ⟨hL, hhL, HL⟩ := exists_restartShearEntrance_connection
  refine ⟨min hU hL, lt_min hhU hhL, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aU, haU, HaU⟩ := HU h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aL, haL, HaL⟩ := HL h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min aU aL, lt_min haU haL, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s
  by_cases hv : 1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2
  · obtain ⟨_, hp, hG, hphase, ht⟩ :=
      HaU a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ h₃P ρ hρ hv
    exact ⟨hp, hG, hphase, ht⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hp, hG, hphase, ht⟩ :=
      HaL a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ (lt_of_not_ge hv)
    exact ⟨hp, hG, hphase, ht⟩
