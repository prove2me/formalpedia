-- Prove2me | solution 1 for BianchiIX.entrancePartialCore_reflection_values
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:41:48.907451+00:00
-- url     : https://prove2.me/submissions/74a7f9e9-3d10-421c-9f53-37b901d5af29

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_ConnectionClockDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturnValues
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_connectionLog_matchingPhase_drift
import Theorems.Thm_BianchiIX_connectionLog_prefix_estimates
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreRadiusReturn_large_regular
import Theorems.Thm_BianchiIX_entranceReturn_active_component
import Theorems.Thm_BianchiIX_entranceReturn_decay
import Theorems.Thm_BianchiIX_entranceReturn_region
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entranceReturn_walls_pos
import Theorems.Thm_BianchiIX_entrance_denom_bounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_connectionReturn_log_clock
import Theorems.Thm_BianchiIX_exists_connection_first_return
import Theorems.Thm_BianchiIX_exists_large_core_exit_derivative
import Theorems.Thm_BianchiIX_exists_large_core_traversal
import Theorems.Thm_BianchiIX_exists_normalized_connection_log_segment
import Theorems.Thm_BianchiIX_exists_partialCore_downward_radius_response
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Theorems.Thm_BianchiIX_projectiveOriginalFlow_restart
import Theorems.Thm_BianchiIX_toProjectiveState_denom_pos
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
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section
open BianchiIX
open Set

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

private theorem BianchiIX.connection_coupling_bounds {u v w : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -u ^ 2 ≤ coupling u v w ∧ coupling u v w ≤ 2 * u := by
  unfold coupling
  constructor
  · nlinarith only [mul_nonneg hu hv.1, mul_nonneg hu hw.1]
  · nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu,
      mul_le_mul_of_nonneg_left hw.2 hu, sq_nonneg u]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_speed_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    μ / 2 ≤ connectionSpeed m u v w ∧ connectionSpeed m u v w ≤ μ := by
  obtain ⟨hc₀, hc₁⟩ := connection_coupling_bounds hu.1 hv hw
  obtain ⟨hm₀, hm₁⟩ := abs_le.mp hm
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionSpeed
  constructor <;> nlinarith only [hc₀, hc₁, hm₀, hm₁, hu.2, hu2, hμ]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_denom_bound {m u v w : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w ∧ 0 < projectiveDenom (-m) u v w := by
  have H : 3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w := by
    dsimp [projectiveDenom, curvature]
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu.1,
      mul_le_mul_of_nonneg_left hw.2 hu.1, sq_nonneg u, sq_nonneg (v - w)]
  exact ⟨H, by nlinarith only [H, hu.2, sq_nonneg m]⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_pos {a b : ℝ} (ha : 0 < a) : 0 < phaseNorm a b :=
  ha.trans_le (phaseNorm_ge ha.le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_defect {a b : ℝ} (ha : 0 < a) :
    phaseNorm a b - a = b ^ 2 / (phaseNorm a b + a) := by
  apply (eq_div_iff (ne_of_gt (add_pos (phaseNorm_pos ha) ha))).mpr
  nlinarith only [phaseNorm_sq a b]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_section_sign (m : ℝ) :
    (coreAngle m 1 < 0 ↔ 1 < m) ∧ (0 < coreAngle m 1 ↔ m < 1) := by
  simp only [coreAngle, div_one, Real.arsinh_neg_iff, Real.arsinh_pos_iff]
  constructor <;> constructor <;> intro h <;> linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_defect_bounds {μ a b : ℝ} (hμ : 0 < μ) (ha : μ / 2 ≤ a) :
    0 ≤ phaseNorm a b - a ∧ phaseNorm a b - a ≤ b ^ 2 / μ := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hnorm := phaseNorm_ge (b := b) ha0.le
  refine ⟨sub_nonneg.mpr hnorm, ?_⟩
  rw [phaseNorm_defect ha0]
  exact div_le_div_of_nonneg_left (sq_nonneg b) hμ (by linarith only [ha, hnorm])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_endpoint_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hu : 0 ≤ u) (hv : 0 ≤ v ∧ v ≤ w)
    (hJ : |matchingPhase m v 1 - matchingPhase μ 1 w| ≤ 20 * u / μ + w ^ 2 / μ ^ 2) :
    |phaseNorm (m - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤ 24 * (u + w ^ 2) / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have he0 := phaseNorm_defect_bounds (b := w) hμ0 (show μ / 2 ≤ μ - 1 by linarith only [hμ])
  have he1 := phaseNorm_defect_bounds (b := v) hμ0
    (show μ / 2 ≤ m + 1 by linarith only [hμ, (abs_le.mp hm).1])
  have hv2 := pow_le_pow_left₀ hv.1 hv.2 2
  have he1' := he1.2.trans (div_le_div_of_nonneg_right hv2 hμ0.le)
  have hid : phaseNorm (m - 1) 1 - phaseNorm (μ + 1) 1 + 2 =
      matchingPhase m v 1 - matchingPhase μ 1 w +
        (phaseNorm (μ - 1) w - (μ - 1)) - (phaseNorm (m + 1) v - (m + 1)) := by
    dsimp [matchingPhase]
    ring
  rw [hid]
  have H := (abs_sub (matchingPhase m v 1 - matchingPhase μ 1 w + (phaseNorm (μ - 1) w - (μ - 1)))
    (phaseNorm (m + 1) v - (m + 1))).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_of_nonneg he0.1, abs_of_nonneg he1.1] at H
  apply (H.trans (add_le_add (add_le_add hJ he0.2) he1')).trans
  have hμsq : μ ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 1)]
  have hsq := div_le_div_of_nonneg_left (sq_nonneg w) hμ0 hμsq
  have huq := div_nonneg hu hμ0.le
  have hwq := div_nonneg (sq_nonneg w) hμ0.le
  calc
    20 * u / μ + w ^ 2 / μ ^ 2 + w ^ 2 / μ + w ^ 2 / μ ≤
        20 * (u / μ) + 3 * (w ^ 2 / μ) := by
      calc
        _ ≤ 20 * u / μ + w ^ 2 / μ + w ^ 2 / μ + w ^ 2 / μ := by gcongr
        _ = _ := by ring
    _ ≤ 24 * (u / μ) + 24 * (w ^ 2 / μ) := by nlinarith only [huq, hwq]
    _ = 24 * (u + w ^ 2) / μ := by ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.core_exit_connection_radial_range {k m : ℝ} (hk : 6 ≤ k) (hm : m < 1)
    (hE : |coreEnergy m 1 - k ^ 2| ≤ 1 / 8) : 4 ≤ -m ∧ k / 2 ≤ -m ∧ -m < k := by
  have hElo := (abs_le.mp hE).1
  have hEhi := (abs_le.mp hE).2
  dsimp [coreEnergy] at hElo hEhi
  have hm4 : 4 ≤ -m := by
    by_contra H
    have hm5 : 1 - m < 5 := by linarith only [H]
    have hs : (1 - m) ^ 2 < 5 ^ 2 :=
      (sq_lt_sq₀ (by linarith only [hm] : 0 ≤ 1 - m) (by norm_num)).mpr hm5
    nlinarith only [hs, hElo, hk, sq_nonneg (k - 6)]
  refine ⟨hm4, ?_, ?_⟩
  · by_contra H
    have hs : (1 - m) ^ 2 < (k / 2 + 1) ^ 2 :=
      (sq_lt_sq₀ (by linarith only [hm] : 0 ≤ 1 - m) (by linarith only [hk])).mpr (by linarith only [H])
    nlinarith only [hs, hElo, hk, sq_nonneg (k - 6)]
  · by_contra H
    have hs : k ^ 2 ≤ (-m) ^ 2 := (sq_le_sq₀ (by linarith only [hk]) (by linarith only [hm4])).mpr (by linarith only [H])
    nlinarith only [hs, hEhi, hm4]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.core_connection_phase_error {k μ K n b : ℝ} (hk : 0 < k) (hμ : 0 < μ)
    (hkμ : k ≤ 2 * μ) (hb : 0 ≤ b)
    (hcore : |K - k| ≤ 16 / k * b) (hconn : |n - K + 2| ≤ 24 * b / μ) :
    |n - (k - 2)| ≤ 64 * b / k := by
  have H : 24 * b / μ ≤ 48 * b / k := by
    apply (div_le_div_iff₀ hμ hk).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hkμ hb]
  calc
    _ = |(n - K + 2) + (K - k)| := by congr 1; ring
    _ ≤ |n - K + 2| + |K - k| := abs_add_le _ _
    _ ≤ 48 * b / k + 16 / k * b := add_le_add (hconn.trans H) hcore
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.core_connection_phase_decrease {k n u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k)
    (herr : |n - (k - 2)| ≤ 64 * (u + w ^ 2) / k) : 1 ≤ k - n ∧ k - n ≤ 3 := by
  have hk0 : 0 < k := by linarith only [hk]
  have hu0 : u ≤ 1 / 10000 := hu.2.trans (div_le_self (by norm_num) (by linarith only [hk]))
  have hw0 : w ≤ 1 / 10000 := hw.2.trans (div_le_self (by norm_num) (by linarith only [hk]))
  have hw2 : w ^ 2 ≤ w := by nlinarith only [hw.1, hw0]
  have H : 64 * (u + w ^ 2) / k ≤ 1 := (div_le_one hk0).mpr (by linarith only [hu0, hw0, hw2, hk])
  have Ha := abs_le.mp (herr.trans H)
  constructor <;> linarith only [Ha.1, Ha.2]

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

private theorem BianchiIX.projectiveOriginalField_connectionLog {y : ProjectiveState} (hD : connectionClockRate y ≠ 0) :
    projectiveOriginalField y = connectionOriginalClockRate y • connectionLogField y := by
  unfold connectionOriginalClockRate connectionLogField projectiveOriginalField
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hD, mul_one]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreAngle_entry_eq_neg_arcosh {m : ℝ} (hm : 1 < m) :
    coreAngle m 1 = -Real.arcosh (coreRadius m 1) := by
  have H := Real.arcosh_cosh (neg_nonneg.mpr ((coreAngle_section_sign m).1.mpr hm).le)
  rw [Real.cosh_neg, cosh_coreAngle (by norm_num : (0 : ℝ) < 1), div_one] at H
  linarith

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
open Set Filter
open scoped Topology

private theorem BianchiIX.toProjectiveState_wall_sign {x : NormalizedState} (hA : 0 < 1 + x 0) (i : Fin 3) :
    (toProjectiveState x i.succ = 0 ↔ wallValue i x = 0) ∧
      (0 ≤ toProjectiveState x i.succ ↔ 0 ≤ wallValue i x) := by
  have heq : toProjectiveState x i.succ = Real.sqrt 3 * wallValue i x / (1 + x 0) := by
    fin_cases i <;> rfl
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [heq]
  constructor
  · simp only [div_eq_zero_iff, mul_eq_zero, ne_of_gt hsqrt, ne_of_gt hA, false_or, or_false]
  · rw [div_eq_mul_inv, mul_nonneg_iff_of_pos_right (inv_pos.mpr hA), mul_nonneg_iff_of_pos_left hsqrt]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_projective_wall_sign {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (β t i.succ = 0 ↔ β s i.succ = 0) ∧ (0 ≤ β t i.succ ↔ 0 ≤ β s i.succ) := by
  have H := normalized_wall_sign (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
    (fun _ hh => hasDerivAt_normalizedMaxCurve hh) hs ht i
  exact ⟨(toProjectiveState_wall_sign hAt i).1.trans (H.1.trans (toProjectiveState_wall_sign hAs i).1.symm),
    (toProjectiveState_wall_sign hAt i).2.trans (H.2.trans (toProjectiveState_wall_sign hAs i).2.symm)⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.connectionLog_endpoint_phase_bound {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hinit : -Y a 0 = μ) (hV : Y a 2 = 1) (hhit : Y b 3 = 1) :
    |phaseNorm (-Y b 0 - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤ 24 * (Y a 1 + (Y a 3) ^ 2) / μ := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hentry : Y a 1 ≤ Y a 2 := by rw [hV]; linarith only [(hu a ha).2]
  have hp := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).2.2.2.1
  have hexp : Real.exp (-2 * (b - a) / μ) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.mpr hab))
      (by linarith only [hμ])
  have hvw : Y b 2 ≤ Y a 3 := by
    rw [hV, hhit, mul_one, one_mul] at hp
    exact hp.trans ((mul_le_mul_of_nonneg_left hexp (hw a ha).1).trans_eq (mul_one _))
  have hJ := connectionLog_matchingPhase_drift hab hμ hY hm hu hv hw hentry
  rw [hinit, hV, hhit, one_mul] at hJ
  exact matchingPhase_endpoint_bound hμ (hm b hb) (hu a ha).1 ⟨(hv b hb).1.le, hvw⟩ hJ

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_projective_wall_pos {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) (hi : 0 < toProjectiveState (normalizedMaxCurve x t₀ s) i.succ) :
    0 < toProjectiveState (normalizedMaxCurve x t₀ t) i.succ := by
  have H := normalized_projective_wall_sign hs ht hAs hAt i
  have hne : toProjectiveState (normalizedMaxCurve x t₀ t) i.succ ≠ 0 :=
    fun h => (ne_of_gt hi) (H.1.mp h)
  exact lt_of_le_of_ne (H.2.mpr hi.le) hne.symm

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

private theorem BianchiIX.entranceRegion_phase {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    4 / 5 * k ≤ y 0 - 1 ∧ y 0 - 1 ≤ 101 / 100 * k :=
  entrance_phase_bounds hk hy.1 hy.2.1 hy.2.2.2.1

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

private theorem BianchiIX.hasDerivAt_projectiveOriginalFlow_connectionLog {y : ProjectiveState} {t₀ z : ℝ}
    {q : ℝ → ℝ} (hD : 0 < projectiveStateDenom y)
    (ht : q z ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ (q z) 0)
    (hclock : connectionClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0)
    (hq : HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z))) z) :
    HasDerivAt (fun r => projectiveOriginalFlow y t₀ (q r))
      (connectionLogField (projectiveOriginalFlow y t₀ (q z))) z := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ (q z)) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have hr : connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (ne_of_gt (toProjectiveState_denom_pos hA hc))) hclock
  have H := (hasDerivAt_projectiveOriginalFlow_time hD ht hA).scomp z hq
  rw [projectiveOriginalField_connectionLog hclock] at H
  simpa only [Function.comp_def, smul_smul, one_div_mul_cancel hr, one_smul] using H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_connection_endpoint_phase_bound {x : NormalizedState} {t₀ μ s t : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    (∀ u ∈ Icc s t, connectionRegion μ (β u)) → -β s 0 = μ → β s 2 = 1 →
    0 < β s 3 → β t 3 = 1 →
    |phaseNorm (-β t 0 - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤ 24 * (β s 1 + (β s 3) ^ 2) / μ := by
  intro β hregion hinit hV hw hhit
  obtain ⟨hL, q, hq0, hqt, hqmap, _, hqode⟩ :=
    exists_normalized_connection_log_segment hc hμ hs hst hA hregion hw
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hdom (u : ℝ) (hu : u ∈ Icc s t) : u ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
  have hvpos (u : ℝ) (hu : u ∈ Icc s t) : 0 < β u 2 := by
    apply normalized_projective_wall_pos (hdom s hsm) (hdom u hu) (hA s hsm) (hA u hu) 1
    change 0 < β s 2
    rw [hV]
    norm_num
  have H := connectionLog_endpoint_phase_bound hL hμ hqode
    (fun z hz => (hregion _ (hqmap hz)).1)
    (fun z hz => (hregion _ (hqmap hz)).2.1)
    (fun z hz => ⟨hvpos _ (hqmap hz), (hregion _ (hqmap hz)).2.2.1.2⟩)
    (fun z hz => (hregion _ (hqmap hz)).2.2.2)
    (by change -β (q 0) 0 = μ; rwa [hq0])
    (by change β (q 0) 2 = 1; rwa [hq0])
    (by change β (q _) 3 = 1; rwa [hqt])
  simpa only [hq0, hqt] using H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_connection_phase_bound {μ u w : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hw : 0 < w ∧ w ≤ 1 / 10000) :
    let x := fromProjectiveState (connectionEntry μ u w)
    let β := fun t => toProjectiveState (normalizedMaxCurve x 0 t)
    ∃ T > (0 : ℝ),
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧ β t 3 = 1} T ∧
      (∀ t ∈ Icc 0 T, 3 / (2 * μ ^ 2) ≤ 1 + normalizedMaxCurve x 0 t 0 ∧ connectionRegion μ (β t)) ∧
      |phaseNorm (-β T 0 - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤ 24 * (u + w ^ 2) / μ := by
  intro x β
  obtain ⟨T, hT, hfirst, hprefix, _⟩ := exists_connection_first_return hμ hu hw
  have hμ1 : 1 ≤ μ := by linarith only [hμ]
  have hu' : 0 ≤ u ∧ u ≤ 1 / 10000 := ⟨hu.1, hu.2.trans (div_le_self (by norm_num) hμ1)⟩
  have hw' : 0 ≤ w ∧ w ≤ 1 := ⟨hw.1.le, hw.2.trans (by norm_num)⟩
  have hD : 0 < projectiveStateDenom (connectionEntry μ u w) :=
    (connection_denom_bound (m := μ) (v := 1) hu' (by norm_num) hw').2
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hβ0 : β 0 = connectionEntry μ u w := by
    dsimp [β]
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState (ne_of_gt hD)
  have hA (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < 1 + normalizedMaxCurve x 0 t 0 :=
    lt_of_lt_of_le (by positivity) (hprefix t ht).1
  have H := normalized_connection_endpoint_phase_bound hc hμ (le_refl 0) hT.le hA
    (fun t ht => (hprefix t ht).2)
    (show -β 0 0 = μ by rw [hβ0]; simp [connectionEntry])
    (show β 0 2 = 1 by rw [hβ0]; rfl)
    (show 0 < β 0 3 by simpa [hβ0, connectionEntry] using hw.1) hfirst.1.2.2
  refine ⟨T, hT, hfirst, hprefix, ?_⟩
  change |phaseNorm (-β T 0 - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤
    24 * (β 0 1 + (β 0 3) ^ 2) / μ at H
  simpa [hβ0, connectionEntry] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadius_coreRadiusEntry {Y : CoreAngleState} (hk : 1 < Y 0) :
    coreRadius (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 := by
  have hk0 : 0 < Y 0 := lt_trans zero_lt_one hk
  have hsq := Real.sq_sqrt (by nlinarith only [hk] : 0 ≤ Y 0 ^ 2 - 1)
  have he : coreEnergy (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 ^ 2 := by
    dsimp [coreRadiusEntry, coreEnergy]
    nlinarith only [hsq]
  rw [coreRadius, he, Real.sqrt_sq hk0.le]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreRadiusEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreRadiusEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreRadiusEntry] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusEntry_region {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    coreRegion (Y 0) (coreRadiusEntry Y) := by
  have hR := coreRadius_coreRadiusEntry (by linarith only [hk] : 1 < Y 0)
  have he := coreRadius_sq (coreRadiusEntry Y 0) (coreRadiusEntry Y 2)
  rw [hR] at he
  refine ⟨?_, le_rfl, hu, ?_⟩
  · rw [← he, sub_self, abs_zero]
    norm_num
  · simpa [coreRadiusEntry] using hw

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connection_entry_denom_pos {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    0 < projectiveStateDenom (connectionEntry (p 0) (p 1) (p 2)) := by
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ 1 / 10000 :=
    ⟨hu.1, hu.2.trans (div_le_self (by norm_num) (by linarith only [hμ]))⟩
  exact (connection_denom_bound (m := p 0) (v := 1) hu' (by norm_num)
    ⟨hw.1.le, hw.2.trans (by norm_num)⟩).2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.entrance_initial_denom_pos {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) : 0 < projectiveStateDenom y := by
  have hr : |coreRadius (y 0) (y 2) - coreRadius (y 0) (y 2)| ≤ coreRadius (y 0) (y 2) / 100 := by
    rw [sub_self, abs_zero]
    linarith
  exact (entrance_denom_bounds hk (entrance_phase_bounds hk hm hr ⟨hv.1.le, hv.2.le⟩)
    hu ⟨hv.1.le, hv.2.le⟩ hw).1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connectionReturn_growing_component {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    connectionReturnState p 3 = 1 ∧ ∀ v : ConnectionParameters, fderiv ℝ connectionReturnState p v 3 = 0 := by
  have H := connectionReturn_regular hμ hu hw
  have heq : (fun q => connectionReturnState q 3) =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
    filter_upwards [H.2.2.2.2.2] with q hq
    exact hq.1.1.2.2
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) p).congr_of_eventuallyEq heq
  have hc := (hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) (connectionReturnState p)).comp p
    ((H.2.2.1.differentiableAt (by norm_num)).hasFDerivAt)
  refine ⟨heq.self_of_nhds, ?_⟩
  intro v
  have hlinear := hc.unique hd
  exact congrArg (fun L : ConnectionParameters →L[ℝ] ℝ => L v) hlinear

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.connectionReturn_control {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    0 < connectionReturnTime p ∧ ∀ t ∈ Icc 0 (connectionReturnTime p),
      3 / (2 * (p 0) ^ 2) ≤ 1 + normalizedMaxCurve (connectionInitialState p) 0 t 0 ∧
        connectionRegion (p 0) (toProjectiveState (normalizedMaxCurve (connectionInitialState p) 0 t)) := by
  obtain ⟨T, hT, hfirst, hprefix, _⟩ := exists_connection_first_return hμ hu hw
  have heq : connectionReturnTime p = T := hfirst.csInf_eq
  rw [heq]
  exact ⟨hT, hprefix⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.connectionReturn_phase_bound {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    |connectionReturnPhaseError p| ≤ 24 * (p 1 + (p 2) ^ 2) / p 0 := by
  obtain ⟨T, _, hfirst, _, hbound⟩ := exists_connection_phase_bound hμ hu hw
  have heq : connectionReturnTime p = T := hfirst.csInf_eq
  simpa only [connectionReturnPhaseError, connectionReturnState, heq, connectionInitialState] using hbound

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.connectionReturn_wall_pos {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    0 < connectionReturnState p 2 ∧ (0 < p 1 → 0 < connectionReturnState p 1) := by
  have hvalid := (connectionReturn_regular hμ hu hw).1
  have hT := hvalid.1.1.1
  have hD := connection_entry_denom_pos hμ hu hw
  have hinit : toProjectiveState (normalizedMaxCurve (connectionInitialState p) 0 0) =
      connectionEntry (p 0) (p 1) (p 2) := by
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState (ne_of_gt hD)
  have hs := hvalid.2.1 0 ⟨le_rfl, hT.le⟩
  have ht := hvalid.2.1 (connectionReturnTime p) ⟨hT.le, le_rfl⟩
  constructor
  · apply normalized_projective_wall_pos hs.1 ht.1 hs.2 ht.2 1
    simp [hinit, connectionEntry]
  · intro hu0
    apply normalized_projective_wall_pos hs.1 ht.1 hs.2 ht.2 0
    simpa [hinit, connectionEntry] using hu0

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.connectionReturn_exponential_decay {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    let L := -Real.log (p 2)
    connectionReturnState p 1 ≤ p 1 * Real.exp (-p 0 * L / 2) ∧
    connectionReturnState p 2 ≤ p 2 * Real.exp (-2 * L / p 0) := by
  intro L
  let y := connectionEntry (p 0) (p 1) (p 2)
  obtain ⟨hL, q, hq0, hqL, H⟩ := exists_connectionReturn_log_clock hμ hu hw
  change q L = connectionReturnTime p at hqL
  let Y := fun z => projectiveOriginalFlow y 0 (q z)
  have hden := connection_entry_denom_pos hμ ⟨hu.1.le, hu.2⟩ hw
  have hm z hz := (H z hz).2.2.1.1
  have hU z hz := (H z hz).2.2.1.2.1
  have hV z hz := And.intro (H z hz).2.2.2.2.1 (H z hz).2.2.1.2.2.1.2
  have hW z hz := (H z hz).2.2.1.2.2.2
  have hD (z : ℝ) (hz : z ∈ Icc 0 L) : connectionClockRate (Y z) ≠ 0 := by
    have Hs := (connection_speed_bounds hμ (hm z hz) (hU z hz)
      ⟨(hV z hz).1.le, (hV z hz).2⟩ (hW z hz)).1
    change p 0 / 2 ≤ connectionClockRate (Y z) at Hs
    linarith only [Hs, hμ]
  have hY z hz := hasDerivAt_projectiveOriginalFlow_connectionLog (y := y) (t₀ := 0) (q := q) (z := z)
    hden (H z hz).1 (H z hz).2.1 (hD z hz) (H z hz).2.2.2.2.2.2
  have hinit : Y 0 = y := by dsimp [Y]; rw [hq0, projectiveOriginalFlow_initial hden]
  have hend : Y L = connectionReturnState p := by dsimp [Y]; rw [hqL]; rfl
  have hentry : Y 0 1 ≤ Y 0 2 := by
    rw [hinit]
    change p 1 ≤ 1
    have Hs := (le_div_iff₀ (show 0 < p 0 by linarith only [hμ])).mp hu.2
    nlinarith only [Hs, hμ, hu.1]
  have HP := connectionLog_prefix_estimates hL hμ hY hm hU hV hW hentry
  constructor
  · have Hs := HP.2.1
    change Y L 1 ≤ Y 0 1 * Real.exp (-p 0 * (L - 0) / 2) at Hs
    simpa [hinit, hend, y, connectionEntry] using Hs
  · have Hs := HP.2.2.2.1
    change Y L 2 * Y L 3 ≤ Y 0 2 * Y 0 3 * Real.exp (-2 * (L - 0) / p 0) at Hs
    rw [hend, hinit, (connectionReturn_growing_component hμ ⟨hu.1.le, hu.2⟩ hw).1] at Hs
    simpa [y, connectionEntry] using Hs

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceReturn_walls_nonincreasing {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    entranceReturnState y 1 ≤ y 1 ∧ entranceReturnState y 3 ≤ y 3 := by
  have H := entranceReturn_decay hk hm hu hv hw
  have hk0 : 0 < coreRadius (y 0) (y 2) := by linarith only [hk]
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hEs : Real.exp (-coreRadius (y 0) (y 2) * -Real.log (y 2) / 3) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk0.le) hL) (by norm_num))
  have hEw : Real.exp (-(-Real.log (y 2)) / coreRadius (y 0) (y 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hk0.le)
  constructor
  · exact H.1.trans ((mul_le_mul_of_nonneg_left hEs (mul_nonneg hu.1 hv.1.le)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hv.2.le hu.1]))
  · exact H.2.trans ((mul_le_mul_of_nonneg_left hEw (mul_nonneg hw.1 hv.1.le)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hv.2.le hw.1]))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceReturn_partialCore_entry {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    let k := coreRadius (y 0) (y 2)
    let z := entranceReturnState y
    let κ := coreRadius (z 0) (z 2)
    6 ≤ κ ∧ (99 / 100 * k ≤ κ ∧ κ ≤ 101 / 100 * k) ∧
      z 2 = 1 ∧ 1 < z 0 ∧ coreRegion κ z ∧
      (0 ≤ z 1 ∧ z 1 ≤ y 1) ∧ (0 ≤ z 3 ∧ z 3 ≤ y 2 * y 3) ∧
      z 1 + z 2 * z 3 ≤ η / κ ∧ projectiveCoreAngle z = -Real.arcosh κ := by
  intro k z κ
  have hk' : 7 / 4 ≤ k := by linarith only [hk]
  have hk0 : 0 < k := by linarith only [hk]
  have HE := (entranceReturn_regular hk' hm hu hv hw).1
  have HR := entranceReturn_region hk' hm hu hv hw _ ⟨HE.1.1.1.le, le_rfl⟩
  change entranceRegion k z at HR
  have hκ : 99 / 100 * k ≤ κ ∧ κ ≤ 101 / 100 * k := by
    have H := abs_le.mp HR.2.1
    change - (k / 100) ≤ κ - k ∧ κ - k ≤ k / 100 at H
    constructor <;> linarith only [H.1, H.2]
  have hκ6 : 6 ≤ κ := by linarith only [hk, hκ.1]
  have hκ0 : 0 < κ := by linarith only [hκ6]
  have hhit : z 2 = 1 := (entranceReturn_active_component hk' hm hu hv hw).1
  have hm' : 1 < z 0 := by
    have H := (entranceRegion_phase hk' HR).1
    linarith only [H, hk]
  have hU := (entranceReturn_walls_nonincreasing hk' hm hu hv hw).1
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hExp : Real.exp (-(-Real.log (y 2)) / k) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hk0.le)
  have hW : z 3 ≤ y 2 * y 3 := (entranceReturn_decay hk' hm hu hv hw).2.trans
    ((mul_le_of_le_one_right (mul_nonneg hw.1 hv.1.le) hExp).trans_eq (mul_comm _ _))
  have hsum : z 1 + z 2 * z 3 ≤ η / κ := by
    rw [hhit, one_mul]
    exact (add_le_add hU hW).trans (hsmall.trans
      (div_le_div_of_nonneg_left hη.1.le hκ0 (by linarith only [hκ.2, hk0])))
  have hprod : 0 ≤ z 2 * z 3 := mul_nonneg HR.2.2.2.1.1 HR.2.2.2.2.1
  refine ⟨hκ6, hκ, hhit, hm', partialCoreEntry_region hκ6 (by rw [hhit])
    HR.2.2.1.1 hprod hη.2 hsum, ⟨HR.2.2.1.1, hU⟩, ⟨HR.2.2.2.2.1, hW⟩, hsum, ?_⟩
  change coreAngle (z 0) (z 2) = -Real.arcosh (coreRadius (z 0) (z 2))
  rw [hhit]
  exact coreAngle_entry_eq_neg_arcosh hm'

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
open Set Filter
open scoped Topology

private theorem BianchiIX.entranceReturn_downward_restart {y : ProjectiveState} {T : ℝ}
    (hD : 0 < projectiveStateDenom y) (HE : entranceReturnValid y)
    (HT : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState (entranceReturnState y)) 0 ∧
      projectiveOriginalFlow (entranceReturnState y) 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState (entranceReturnState y)) 0 t < 0} T) :
    IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧ normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0}
        (entranceReturnTime y + T) ∧
    partialCoreDownwardReturnTime y = entranceReturnTime y + T ∧
    partialCoreDownwardReturnState y = toCoreAngleState (projectiveOriginalFlow (entranceReturnState y) 0 T) := by
  let S := entranceReturnTime y
  let z := entranceReturnState y
  have hS : 0 < S := HE.1.1.1
  have hT : 0 < T := HT.1.1
  have hA := (HE.2.1 S ⟨hS.le, le_rfl⟩).2
  have hc := fromProjectiveState_constraint hD.ne'
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hS.le
  have hbase : fromProjectiveState z = normalizedMaxCurve (fromProjectiveState y) 0 S :=
    fromProjectiveState_toProjectiveState hA.ne' ((normalizedMaxCurve_constraint hdom).trans hc)
  have hcz : stateConstraint (fromProjectiveState z) = 1 := by
    rw [hbase]
    exact (normalizedMaxCurve_constraint hdom).trans hc
  have Hflow (t : ℝ) (ht : 0 ≤ t) :
      normalizedMaxCurve (fromProjectiveState z) 0 t = normalizedMaxCurve (fromProjectiveState y) 0 (S + t) := by
    rw [hbase]
    have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hdom)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hS.le))
    simpa only [zero_add, add_comm t S] using H
  have Hproj (t : ℝ) (ht : 0 ≤ t) : projectiveOriginalFlow z 0 t = projectiveOriginalFlow y 0 (S + t) :=
    congrArg toProjectiveState (Hflow t ht)
  have Hrate (t : ℝ) (ht : 0 ≤ t) :
      normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t =
        normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 (S + t) := by
    unfold normalizedEventRate
    rw [Hflow t ht]
  have Hleast : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧ normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0}
        (S + T) := by
    refine ⟨⟨add_pos hS hT, normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_pos hS hT).le, ?_, ?_⟩, ?_⟩
    · rw [← Hproj T hT.le]
      exact HT.1.2.2.1
    · rw [← Hrate T hT.le]
      exact HT.1.2.2.2
    · intro t ht
      by_cases htS : t ≤ S
      · have H := HE.2.2.2 t ⟨ht.1.le, htS⟩
        linarith only [H, ht.2.2.2]
      · have hsub : 0 < t - S := sub_pos.mpr (lt_of_not_ge htS)
        have HP := Hproj (t - S) hsub.le
        have HR := Hrate (t - S) hsub.le
        rw [add_sub_cancel] at HP HR
        have H := HT.2 ⟨hsub, normalizedMaxDomain_contains_Ici_of_constraint hcz 0 hsub.le,
          by rw [HP]; exact ht.2.2.1, by rw [HR]; exact ht.2.2.2⟩
        linarith only [H]
  have Htime := partialCoreDownwardReturnTime_eq Hleast
  refine ⟨Hleast, Htime, ?_⟩
  unfold partialCoreDownwardReturnState
  rw [Htime, ← Hproj T hT.le]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.entrancePartialCore_downward_regular {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    let z := entranceReturnState y
    IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧ normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0}
        (partialCoreDownwardReturnTime y) ∧
      partialCoreDownwardReturnTime y = entranceReturnTime y + partialCoreDownwardReturnTime z ∧
      partialCoreDownwardReturnState y = partialCoreDownwardReturnState z ∧
      ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧ ContDiffAt ℝ 2 partialCoreDownwardReturnState y ∧
      (partialCoreDownwardReturnTime =ᶠ[𝓝 y] fun w => entranceReturnTime w + partialCoreDownwardReturnTime (entranceReturnState w)) ∧
      (partialCoreDownwardReturnState =ᶠ[𝓝 y] fun w => partialCoreDownwardReturnState (entranceReturnState w)) := by
  intro z
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [hk]
  have HE := entranceReturn_regular hk' hm hu hv hw
  obtain ⟨hκ, _, hhit, hmz, hregion, _⟩ := entranceReturn_partialCore_entry hk hm hu hv hw hη hsmall
  have HC := partialCoreDownwardReturn_regular hκ hregion rfl (Or.inr ⟨hhit, hmz.le⟩)
  have hD := entrance_initial_denom_pos hk' hm hu hv hw
  have hDc : Continuous projectiveStateDenom := by unfold projectiveStateDenom projectiveDenom curvature; fun_prop
  have Hnear := HE.2.2.1.continuousAt.tendsto.eventually HC.2.2.2.1
  have Hboth : ∀ᶠ w in 𝓝 y,
      partialCoreDownwardReturnTime w = entranceReturnTime w + partialCoreDownwardReturnTime (entranceReturnState w) ∧
      partialCoreDownwardReturnState w = partialCoreDownwardReturnState (entranceReturnState w) := by
    filter_upwards [hDc.continuousAt.eventually (lt_mem_nhds hD), HE.2.2.2.2.2, Hnear] with w hd he hc
    exact (entranceReturn_downward_restart hd he hc.1).2
  have Htime := Hboth.mono fun _ h => h.1
  have Hstate := Hboth.mono fun _ h => h.2
  have Hbase := entranceReturn_downward_restart hD HE.1 HC.2.2.2.1.self_of_nhds.1
  have ht : ContDiffAt ℝ 2 partialCoreDownwardReturnTime y :=
    (HE.2.1.add (ContDiffAt.comp (g := partialCoreDownwardReturnTime) y HC.2.1 HE.2.2.1)).congr_of_eventuallyEq Htime
  have hz : ContDiffAt ℝ 2 partialCoreDownwardReturnState y :=
    (ContDiffAt.comp (g := partialCoreDownwardReturnState) y HC.2.2.1 HE.2.2.1).congr_of_eventuallyEq Hstate
  refine ⟨?_, Htime.self_of_nhds, Hstate.self_of_nhds, ht, hz, Htime, Hstate⟩
  rw [Htime.self_of_nhds]
  exact Hbase.1

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreExitConnectionParameters_of_exit {y : ProjectiveState} (hM : y 0 < 1) (hV : y 2 = 1) :
    coreExitConnectionParameters (toCoreAngleState y) = ![-y 0, y 1, y 3] := by
  have hs : (toCoreAngleState y 0) ^ 2 - 1 = (y 0 - 1) ^ 2 := by
    change coreRadius (y 0) (y 2) ^ 2 - 1 = _
    rw [coreRadius_sq, hV]
    dsimp [coreEnergy]
    ring
  ext i
  fin_cases i
  · change Real.sqrt ((toCoreAngleState y 0) ^ 2 - 1) - 1 = -y 0
    rw [hs, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hM] : y 0 - 1 < 0)]
    ring
  · rfl
  · change y 2 * y 3 = y 3
    rw [hV, one_mul]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadiusEntry_reflected_exit {y : ProjectiveState} (hM : 1 < -y 0) (hW : y 3 = 1) :
    coreRadiusEntry ![phaseNorm (-y 0 - 1) 1, y 1, y 2] = projectiveReflection y := by
  have hs : phaseNorm (-y 0 - 1) 1 ^ 2 - 1 = (-y 0 - 1) ^ 2 := by
    rw [phaseNorm_sq]
    ring
  ext i
  fin_cases i
  · change 1 + Real.sqrt (phaseNorm (-y 0 - 1) 1 ^ 2 - 1) = -y 0
    rw [hs, Real.sqrt_sq (by linarith only [hM])]
    ring
  · rfl
  · exact hW.symm
  · rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreReturn_connection_data {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hu : 0 < Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 < Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} (τ Y)) :
    let y := projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y)
    let p := coreConnectionParameters τ Y
    y = connectionEntry (p 0) (p 1) (p 2) ∧
      (4 ≤ p 0 ∧ Y 0 / 2 ≤ p 0 ∧ p 0 < Y 0) ∧
      (0 < p 1 ∧ p 1 ≤ Y 1) ∧ (0 < p 2 ∧ p 2 ≤ Y 2) ∧
      |phaseNorm (p 0 + 1) 1 - Y 0| ≤ 16 / Y 0 * (Y 1 + Y 2 ^ 2) ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 (τ Y) 0 := by
  intro y p
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hu' : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0 := ⟨hu.1.le, hu.2⟩
  have hw' : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0 := ⟨hw.1.le, hw.2⟩
  obtain ⟨T, _, hfirstT, hreg, hm, _, _, hphase, hU, hW, _⟩ := exists_large_core_traversal hk hu' hw'
  have hT : T = τ Y := hfirstT.unique hfirst
  subst T
  have ht : τ Y ∈ Icc 0 (τ Y) := ⟨hfirst.1.1.le, le_rfl⟩
  have hr : coreRegion (Y 0) y := (hreg (τ Y) ht).2
  have hV : y 2 = 1 := hfirst.1.2
  have hM : y 0 < 1 := hm
  have hp : p = ![-y 0, y 1, y 3] := coreExitConnectionParameters_of_exit hM hV
  have hrange := core_exit_connection_radial_range hk hM (by simpa only [hV] using hr.1)
  have hentry : y = connectionEntry (p 0) (p 1) (p 2) := by
    rw [hp]
    ext i
    fin_cases i <;> simp [connectionEntry, hV]
  have hD := (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu' hw')).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  have hpos (i : Fin 3) (hi : 0 < coreRadiusEntry Y i.succ) : 0 < y i.succ := by
    apply normalized_projective_wall_pos (initial_mem_normalizedMaxDomain _ 0)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hfirst.1.1.le)
      (hreg 0 ⟨le_rfl, hfirst.1.1.le⟩).1 (hreg (τ Y) ht).1 i
    change 0 < projectiveOriginalFlow (coreRadiusEntry Y) 0 0 i.succ
    rw [projectiveOriginalFlow_initial hD]
    exact hi
  have hUp : 0 < y 1 := hpos 0 hu.1
  have hWp : 0 < y 3 := hpos 2 hw.1
  have hUle : y 1 ≤ Y 1 := hU.trans ((mul_le_mul_of_nonneg_right
    (Real.exp_le_one_iff.mpr (by linarith only [hk] : -Y 0 / 40 ≤ 0)) hu.1.le).trans_eq (one_mul _))
  have hWle : y 3 ≤ Y 2 := hW.trans ((mul_le_mul_of_nonneg_right
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))) hw.1.le).trans_eq (one_mul _))
  have heq : phaseNorm (p 0 + 1) 1 = coreRadius (y 0) (y 2) := by
    rw [hp, hV]
    dsimp [phaseNorm, coreRadius, coreEnergy]
    congr 1
    ring
  refine ⟨hentry, ?_, ?_, ?_, ?_, (hreg (τ Y) ht).1⟩
  · simpa only [hp, Matrix.cons_val_zero] using hrange
  · exact ⟨hUp, hUle⟩
  · simpa [hp] using And.intro hWp hWle
  · rw [heq]
    exact hphase

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreReturn_connection_domain {Y : CoreAngleState} {τ : CoreAngleState → ℝ} {ε : ℝ}
    (hk : 6 ≤ Y 0) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hu : 0 < Y 1 ∧ Y 1 ≤ ε / Y 0) (hw : 0 < Y 2 ∧ Y 2 ≤ ε / Y 0)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} (τ Y)) :
    let p := coreConnectionParameters τ Y
    4 ≤ p 0 ∧ (0 < p 1 ∧ p 1 ≤ ε / p 0) ∧ (0 < p 2 ∧ p 2 ≤ ε) := by
  intro p
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hu' : 0 < Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right hε.2 hk0.le)⟩
  have hw' : 0 < Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0 :=
    ⟨hw.1, hw.2.trans (div_le_div_of_nonneg_right hε.2 hk0.le)⟩
  obtain ⟨_, hμ, hpU, hpW, _⟩ := coreReturn_connection_data hk hu' hw' hfirst
  refine ⟨hμ.1, ⟨hpU.1, ?_⟩, ⟨hpW.1, ?_⟩⟩
  · exact hpU.2.trans (hu.2.trans (div_le_div_of_nonneg_left hε.1.le (by linarith only [hμ.1]) hμ.2.2.le))
  · exact hpW.2.trans (hw.2.trans (div_le_self hε.1.le (by linarith only [hk])))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreReflection_actual_step {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hu : 0 < Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 < Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} (τ Y)) :
    let p := coreConnectionParameters τ Y
    let Z := coreReflectionState τ Y
    connectionReturnValid p ∧ 0 < connectionReturnTime p ∧
      coreRadiusEntry Z = projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0
        (connectionReturnTime p + τ Y)) ∧
      |Z 0 - (Y 0 - 2)| ≤ 64 * (Y 1 + Y 2 ^ 2) / Y 0 ∧
      (0 < Z 1 ∧ Z 1 ≤ Y 1) ∧ (0 < Z 2 ∧ Z 2 ≤ Y 2) ∧
      (1 ≤ Y 0 - Z 0 ∧ Y 0 - Z 0 ≤ 3) := by
  intro p Z
  have hk0 : 0 < Y 0 := by linarith only [hk]
  obtain ⟨hy, hμ, hpU, hpW, hphase, hA⟩ := coreReturn_connection_data hk hu hw hfirst
  have hdom := coreReturn_connection_domain (ε := 1 / 10000) hk (by norm_num) hu hw hfirst
  have hμ0 : 0 < p 0 := by linarith only [hμ.1]
  have hU : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0 := hdom.2.1
  have hW : 0 < p 2 ∧ p 2 ≤ 1 / 10000 := hdom.2.2
  have Hvalid := (connectionReturn_regular hμ.1 ⟨hU.1.le, hU.2⟩ hW).1
  have Hcontrol := connectionReturn_control hμ.1 ⟨hU.1.le, hU.2⟩ hW
  have Hpos := connectionReturn_wall_pos hμ.1 ⟨hU.1.le, hU.2⟩ hW
  have Hdec := connectionReturn_exponential_decay hμ.1 hU hW
  have hL : 0 ≤ -Real.log (p 2) := neg_nonneg.mpr (Real.log_nonpos hW.1.le (by linarith only [hW.2]))
  have hstrong : connectionReturnState p 1 ≤ p 1 := Hdec.1.trans
    ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
      (by nlinarith only [hL, hμ0] : -p 0 * (-Real.log (p 2)) / 2 ≤ 0)) hU.1.le).trans_eq (mul_one _))
  have hweak : connectionReturnState p 2 ≤ p 2 := Hdec.2.trans
    ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (by linarith only [hL]) hμ0.le)) hW.1.le).trans_eq (mul_one _))
  have hZu : 0 < Z 1 ∧ Z 1 ≤ Y 1 := ⟨Hpos.2 hU.1, hstrong.trans hpU.2⟩
  have hZw : 0 < Z 2 ∧ Z 2 ≤ Y 2 := ⟨Hpos.1, hweak.trans hpW.2⟩
  have hD := (coreRegion_clock_regular hk (coreRadiusEntry_region hk ⟨hu.1.le, hu.2⟩ ⟨hw.1.le, hw.2⟩)).1
  have Hrestart := projectiveOriginalFlow_restart hD hfirst.1.1.le Hcontrol.1.le hA
  have hendpoint : connectionReturnState p = projectiveOriginalFlow (coreRadiusEntry Y) 0
      (connectionReturnTime p + τ Y) := by
    change projectiveOriginalFlow (connectionEntry (p 0) (p 1) (p 2)) 0 (connectionReturnTime p) = _
    rw [← hy]
    exact Hrestart
  have hregion := (Hcontrol.2 (connectionReturnTime p) ⟨Hcontrol.1.le, le_rfl⟩).2
  change connectionRegion (p 0) (connectionReturnState p) at hregion
  have hM : 1 < -connectionReturnState p 0 := by linarith only [hμ.1, (abs_le.mp hregion.1).1]
  have hentry : coreRadiusEntry Z = projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0
      (connectionReturnTime p + τ Y)) := by
    have H := coreRadiusEntry_reflected_exit hM (connectionReturn_growing_component hμ.1 ⟨hU.1.le, hU.2⟩ hW).1
    exact H.trans (congrArg projectiveReflection hendpoint)
  have hb : p 1 + p 2 ^ 2 ≤ Y 1 + Y 2 ^ 2 := add_le_add hpU.2 (pow_le_pow_left₀ hpW.1.le hpW.2 2)
  have hconn : |Z 0 - phaseNorm (p 0 + 1) 1 + 2| ≤ 24 * (Y 1 + Y 2 ^ 2) / p 0 := by
    exact (connectionReturn_phase_bound hμ.1 ⟨hU.1.le, hU.2⟩ hW).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) hμ0.le)
  have Herr := core_connection_phase_error hk0 hμ0 (by linarith only [hμ.2.1])
    (add_nonneg hu.1.le (sq_nonneg (Y 2))) hphase hconn
  have Hdrop := core_connection_phase_decrease hk ⟨hu.1.le, hu.2⟩ ⟨hw.1.le, hw.2⟩ Herr
  exact ⟨Hvalid, Hcontrol.1, hentry, Herr, hZu, hZw, Hdrop⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusEntry_of_upward_section {y : ProjectiveState}
    (hm : 1 ≤ y 0) (hv : y 2 = 1) :
    coreRadiusEntry (toCoreAngleState y) = y := by
  have he : coreEnergy (y 0) (y 2) = (y 0 - 1) ^ 2 + 1 := by
    simp only [coreEnergy, hv, one_pow]
  have hs : coreRadius (y 0) (y 2) ^ 2 - 1 = (y 0 - 1) ^ 2 := by
    rw [coreRadius, Real.sq_sqrt (by rw [he]; positivity), he]
    ring
  ext i
  fin_cases i
  · change 1 + Real.sqrt (coreRadius (y 0) (y 2) ^ 2 - 1) = y 0
    rw [hs, Real.sqrt_sq (sub_nonneg.mpr hm)]
    ring
  · rfl
  · exact hv.symm
  · change y 2 * y 3 = y 3
    rw [hv, one_mul]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusReturn_downward_eventuallyEq {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    (coreRadiusReturnTime =ᶠ[𝓝 Y] fun Z => partialCoreDownwardReturnTime (coreRadiusEntry Z)) ∧
      (coreReturnState coreRadiusReturnTime =ᶠ[𝓝 Y]
        fun Z => partialCoreDownwardReturnState (coreRadiusEntry Z)) := by
  have hk1 : 1 < Y 0 := by linarith only [hk]
  have he := contDiffAt_coreRadiusEntry 2 hk1
  have hr := coreRadiusReturn_large_regular hk hu hw
  have hd := partialCoreDownwardReturn_regular hk (coreRadiusEntry_region hk hu hw)
    (coreRadius_coreRadiusEntry hk1) (Or.inr ⟨rfl, by
      change (1 : ℝ) ≤ 1 + Real.sqrt (Y 0 ^ 2 - 1)
      linarith only [Real.sqrt_nonneg (Y 0 ^ 2 - 1)]⟩)
  obtain ⟨T, _, hfirst, _, _, _, σ, _, _, _, huniq, _⟩ :=
    exists_large_core_exit_derivative hk hu hw
  have ht : coreRadiusReturnTime Y = T := hr.2.2.2.self_of_nhds.unique hfirst
  have hdt : partialCoreDownwardReturnTime (coreRadiusEntry Y) = T := hd.1.unique hfirst
  have hpair : ContinuousAt (fun Z => (coreRadiusEntry Z, coreRadiusReturnTime Z)) Y :=
    he.continuousAt.prodMk hr.2.1.continuousAt
  have hpaird : ContinuousAt (fun Z =>
      (coreRadiusEntry Z, partialCoreDownwardReturnTime (coreRadiusEntry Z))) Y :=
    he.continuousAt.prodMk (hd.2.1.continuousAt.comp he.continuousAt)
  have hn : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (coreRadiusReturnTime Z) 2 = 1 ↔
        σ (coreRadiusEntry Z) = coreRadiusReturnTime Z := by
    have hlocal : ∀ᶠ z : ProjectiveState × ℝ in
        𝓝 (coreRadiusEntry Y, coreRadiusReturnTime Y),
        projectiveOriginalFlow z.1 0 z.2 2 = 1 ↔ σ z.1 = z.2 := by
      simpa only [ht, coreRadiusEntry] using huniq
    exact hpair.eventually hlocal
  have hnd : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0
        (partialCoreDownwardReturnTime (coreRadiusEntry Z)) 2 = 1 ↔
        σ (coreRadiusEntry Z) = partialCoreDownwardReturnTime (coreRadiusEntry Z) := by
    have hlocal : ∀ᶠ z : ProjectiveState × ℝ in
        𝓝 (coreRadiusEntry Y, partialCoreDownwardReturnTime (coreRadiusEntry Y)),
        projectiveOriginalFlow z.1 0 z.2 2 = 1 ↔ σ z.1 = z.2 := by
      rw [hdt]
      simpa only [coreRadiusEntry] using huniq
    exact hpaird.eventually hlocal
  have hdown := he.continuousAt.tendsto.eventually hd.2.2.2.1
  have htime : coreRadiusReturnTime =ᶠ[𝓝 Y]
      fun Z => partialCoreDownwardReturnTime (coreRadiusEntry Z) := by
    filter_upwards [hn, hnd, hr.2.2.2, hdown] with Z hZ hZd hfull hdown
    exact (hZ.mp hfull.1.2).symm.trans (hZd.mp hdown.1.1.2.2.1)
  refine ⟨htime, ?_⟩
  filter_upwards [htime] with Z hZ
  simp only [coreReturnState, partialCoreDownwardReturnState, hZ]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.entrancePartialCore_fullCore_eventuallyEq {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    (partialCoreDownwardReturnTime =ᶠ[𝓝 y] fun w => entranceReturnTime w +
      coreRadiusReturnTime (toCoreAngleState (entranceReturnState w))) ∧
      (partialCoreDownwardReturnState =ᶠ[𝓝 y] fun w =>
        coreReturnState coreRadiusReturnTime (toCoreAngleState (entranceReturnState w))) := by
  let z := entranceReturnState y
  let X := toCoreAngleState z
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [hk]
  have HE := entranceReturn_regular hk' hm hu hv hw
  obtain ⟨hκ, _, hhit, hmz, _, hU, hW, hsum, _⟩ :=
    entranceReturn_partialCore_entry hk hm hu hv hw hη hsmall
  change 6 ≤ X 0 at hκ
  change z 2 = 1 at hhit
  change 1 < z 0 at hmz
  have hXU : 0 ≤ X 1 := hU.1
  have hXW : 0 ≤ X 2 := by change 0 ≤ z 2 * z 3; rw [hhit, one_mul]; exact hW.1
  have hκ0 : 0 ≤ X 0 := by linarith only [hκ]
  change X 1 + X 2 ≤ η / X 0 at hsum
  have hsum' : X 1 + X 2 ≤ (1 / 10000) / X 0 := hsum.trans
    (div_le_div_of_nonneg_right hη.2 hκ0)
  have HG := coreRadiusReturn_downward_eventuallyEq hκ
    ⟨hXU, (le_add_of_nonneg_right hXW).trans hsum'⟩
    ⟨hXW, (le_add_of_nonneg_left hXU).trans hsum'⟩
  have hcoord : ContinuousAt (fun w => toCoreAngleState (entranceReturnState w)) y :=
    (contDiffAt_toCoreAngleState 2 (by change 0 < z 2; rw [hhit]; norm_num)).continuousAt.comp HE.2.2.1.continuousAt
  have hrecover : ∀ᶠ w in 𝓝 y,
      coreRadiusEntry (toCoreAngleState (entranceReturnState w)) = entranceReturnState w := by
    have hM : ContinuousAt (fun w => entranceReturnState w 0) y :=
      (continuous_apply 0).continuousAt.comp HE.2.2.1.continuousAt
    filter_upwards [HE.2.2.2.2.2, hM.eventually (lt_mem_nhds hmz)] with w he hm'
    apply coreRadiusEntry_of_upward_section hm'.le
    exact he.1.1.2.2
  have HD := entrancePartialCore_downward_regular hk hm hu hv hw hη hsmall
  constructor
  · filter_upwards [HD.2.2.2.2.2.1, hcoord.eventually HG.1, hrecover] with w hd hg hr
    rw [hr] at hg
    exact hd.trans (congrArg (entranceReturnTime w + ·) hg.symm)
  · filter_upwards [HD.2.2.2.2.2.2, hcoord.eventually HG.2, hrecover] with w hd hg hr
    rw [hr] at hg
    exact hd.trans hg.symm

end
end

/-- The same full reflection after a preceding entrance loses between one and three radius units. -/
theorem solution {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 < y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 < y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    let z := entranceReturnState y
    let κ := coreRadius (z 0) (z 2)
    let p := coreExitConnectionParameters (partialCoreDownwardReturnState y)
    let G := connectionReturnPhysicalState p
    κ / 2 ≤ p 0 ∧ (1 ≤ κ - G 0 ∧ κ - G 0 ≤ 3) ∧ κ / 2 ≤ G 0 ∧ G 0 ≤ κ ∧
      |G 0 - (κ - 2)| ≤ 64 * (z 1 + (z 3) ^ 2) / κ ∧
      (0 < G 1 ∧ G 1 ≤ z 1) ∧ (0 < G 2 ∧ G 2 ≤ z 3) := by
  intro z κ p G
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [hk]
  have HE := entranceReturn_regular hk' hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
  obtain ⟨hκ, _, hhit, _, _, _, _, hsum, _⟩ :=
    entranceReturn_partialCore_entry hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩ hη hsmall
  have HP := entranceReturn_walls_pos hk' hm hu hv hw _ ⟨HE.1.1.1.1.le, le_rfl⟩
  change 0 < z 1 ∧ 0 < z 2 ∧ 0 < z 3 at HP
  change z 2 = 1 at hhit
  let X := toCoreAngleState z
  have hκ0 : 0 ≤ κ := by change 6 ≤ κ at hκ; linarith only [hκ]
  have hUX : 0 < X 1 := HP.1
  have hWX : 0 < X 2 := mul_pos HP.2.1 HP.2.2
  have hsum' : X 1 + X 2 ≤ (1 / 10000) / X 0 :=
    hsum.trans (div_le_div_of_nonneg_right hη.2 hκ0)
  have huX : 0 < X 1 ∧ X 1 ≤ (1 / 10000) / X 0 :=
    ⟨hUX, (le_add_of_nonneg_right hWX.le).trans hsum'⟩
  have hwX : 0 < X 2 ∧ X 2 ≤ (1 / 10000) / X 0 :=
    ⟨hWX, (le_add_of_nonneg_left hUX.le).trans hsum'⟩
  have hfirst := (coreRadiusReturn_large_regular hκ ⟨huX.1.le, huX.2⟩ ⟨hwX.1.le, hwX.2⟩).2.2.2.self_of_nhds
  have H := coreReflection_actual_step hκ huX hwX hfirst
  have Hdata := coreReturn_connection_data hκ huX hwX hfirst
  have hstate := (entrancePartialCore_fullCore_eventuallyEq hk hm ⟨hu.1.le, hu.2⟩ hv
    ⟨hw.1.le, hw.2⟩ hη hsmall).2.self_of_nhds
  have hp : p = coreConnectionParameters coreRadiusReturnTime X := congrArg coreExitConnectionParameters hstate
  have hG : G = coreReflectionState coreRadiusReturnTime X := congrArg connectionReturnPhysicalState hp
  have hdrop : 1 ≤ κ - G 0 ∧ κ - G 0 ≤ 3 := by rw [hG]; exact H.2.2.2.2.2.2
  refine ⟨?_, hdrop, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]
    exact Hdata.2.1.2.1
  · change 6 ≤ κ at hκ
    linarith only [hκ, hdrop.2]
  · linarith only [hdrop.1]
  · rw [hG]
    have HV := H.2.2.2.1
    change |coreReflectionState coreRadiusReturnTime X 0 - (κ - 2)| ≤
      64 * (z 1 + (z 2 * z 3) ^ 2) / κ at HV
    simpa only [hhit, one_mul] using HV
  · rw [hG]
    exact H.2.2.2.2.1
  · rw [hG]
    have HW := H.2.2.2.2.2.1
    change 0 < coreReflectionState coreRadiusReturnTime X 2 ∧
      coreReflectionState coreRadiusReturnTime X 2 ≤ z 2 * z 3 at HW
    simpa only [hhit, one_mul] using HW
