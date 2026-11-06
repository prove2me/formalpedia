-- Prove2me | solution 1 for BianchiIX.exists_long_reflection_estimates
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:32:44.747529+00:00
-- url     : https://prove2.me/submissions/9f1f6e04-d2a1-4aed-ad56-f885a46c3b55

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_ConnectionClockDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Analysis_ConnectionLogCoordinates
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturnValues
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_connectionLog_matchingPhase_drift
import Theorems.Thm_BianchiIX_connectionLog_prefix_estimates
import Theorems.Thm_BianchiIX_connectionReturn_phase_cone_amplitude
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_connectionReturn_restart_bounds
import Theorems.Thm_BianchiIX_connectionReturn_unit_cone
import Theorems.Thm_BianchiIX_exists_connectionReturn_log_clock
import Theorems.Thm_BianchiIX_exists_connection_first_return
import Theorems.Thm_BianchiIX_exists_normalized_connection_log_segment
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Theorems.Thm_BianchiIX_toProjectiveState_denom_pos
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open BianchiIX
open Set

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

private theorem BianchiIX.hasDerivAt_matchingPhase {m v w : ℝ → ℝ} {m' v' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) (hmt : 1 < m t) :
    HasDerivAt (fun s => matchingPhase (m s) (v s) (w s))
      (matchingPhaseSlope (m t) (v t) (w t) * m' +
        v t / phaseNorm (m t + 1) (v t) * v' + w t / phaseNorm (m t - 1) (w t) * w') t := by
  have hp : (m t + 1) ^ 2 + v t ^ 2 ≠ 0 := by
    have H : 0 < m t + 1 := by linarith only [hmt]
    positivity
  have hn : (m t - 1) ^ 2 + w t ^ 2 ≠ 0 := by
    have H : 0 < m t - 1 := by linarith only [hmt]
    positivity
  have H := ((((hm.add_const 1).pow 2).add (hv.pow 2)).sqrt hp).add
    ((((hm.sub_const 1).pow 2).add (hw.pow 2)).sqrt hn)
  convert! H.sub hm using 1
  dsimp [matchingPhaseSlope, phaseNorm]
  ring

end
end

section
noncomputable section
open BianchiIX
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem BianchiIX.contDiffAt_matchingPhase_comp {m v w : E → ℝ} {p : E} (n : WithTop ℕ∞)
    (hm : ContDiffAt ℝ n m p) (hv : ContDiffAt ℝ n v p) (hw : ContDiffAt ℝ n w p)
    (hmt : 1 < m p) : ContDiffAt ℝ n (fun q => matchingPhase (m q) (v q) (w q)) p := by
  have hp : (m p + 1) ^ 2 + v p ^ 2 ≠ 0 := by
    have H : 0 < m p + 1 := by linarith only [hmt]
    positivity
  have hn : (m p - 1) ^ 2 + w p ^ 2 ≠ 0 := by
    have H : 0 < m p - 1 := by linarith only [hmt]
    positivity
  exact (((((hm.add contDiffAt_const).pow 2).add (hv.pow 2)).sqrt hp).add
    ((((hm.sub contDiffAt_const).pow 2).add (hw.pow 2)).sqrt hn)).sub hm

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

private theorem BianchiIX.exists_connection_cone_threshold :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ Real.sqrt ε ≤ 1 / 1000000 ∧ ε ≤ Real.exp (-256) := by
  let ε := min ((1 / 1000000 : ℝ) ^ 2) (Real.exp (-256))
  have hε0 : 0 < ε := lt_min (by norm_num) (Real.exp_pos _)
  have hεd : ε ≤ (1 / 1000000 : ℝ) ^ 2 := min_le_left _ _
  refine ⟨ε, hε0, ?_, ?_, min_le_right _ _⟩
  · exact hεd.trans (by norm_num)
  · exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hεd]⟩

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

private theorem BianchiIX.contDiffAt_connectionLogCoordinates (n : WithTop ℕ∞) {y : ProjectiveState}
    (hm : 1 < -y 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) :
    ContDiffAt ℝ n connectionLogCoordinates y := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_matchingPhase_comp n (by fun_prop) (by fun_prop) (by fun_prop) hm
  · exact (contDiff_apply ℝ ℝ 1).contDiffAt.log hu
  · exact (contDiff_apply ℝ ℝ 2).contDiffAt.log hv
  · exact (contDiff_apply ℝ ℝ 3).contDiffAt.log hw

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionLogCoordinates {Y : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y v t) (hm : 1 < -Y t 0) (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) (hw : Y t 3 ≠ 0) :
    HasDerivAt (fun s => connectionLogCoordinates (Y s)) (connectionLogTangent (Y t) v) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_matchingPhase (hasDerivAt_pi.mp hY 0).neg
      (hasDerivAt_pi.mp hY 2) (hasDerivAt_pi.mp hY 3) hm
  · exact (hasDerivAt_pi.mp hY 1).log hu
  · exact (hasDerivAt_pi.mp hY 2).log hv
  · exact (hasDerivAt_pi.mp hY 3).log hw

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionLogCoordinates_fderiv {y : ProjectiveState}
    (hm : 1 < -y 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ connectionLogCoordinates y v = connectionLogTangent y v := by
  have hline : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hd : HasFDerivAt connectionLogCoordinates (fderiv ℝ connectionLogCoordinates y) (y + (0 : ℝ) • v) := by
    simpa using ((contDiffAt_connectionLogCoordinates 1 hm hu hv hw).differentiableAt (by norm_num)).hasFDerivAt
  have H := hasDerivAt_connectionLogCoordinates hline (by simpa using hm)
    (by simpa using hu) (by simpa using hv) (by simpa using hw)
  have HD : HasDerivAt (fun s : ℝ => connectionLogCoordinates (y + s • v))
      (fderiv ℝ connectionLogCoordinates y v) 0 := by
    simpa only [Function.comp_def] using hd.comp_hasDerivAt 0 hline
  simpa only [zero_smul, add_zero] using HD.unique H

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

private theorem BianchiIX.contDiffAt_connectionReturnPhaseError {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    ContDiffAt ℝ 2 connectionReturnPhaseError p := by
  have hstate := (connectionReturn_regular hμ hu hw).2.2.1
  have hcoord : ContDiffAt ℝ 2 (fun q => connectionReturnState q 0) p := contDiffAt_pi.mp hstate 0
  have hleft : ContDiffAt ℝ 2 (fun q => phaseNorm (-connectionReturnState q 0 - 1) 1) p := by
    apply (((hcoord.neg.sub contDiffAt_const).pow 2).add contDiffAt_const).sqrt
    positivity
  have hright : ContDiffAt ℝ 2 (fun q : ConnectionParameters => phaseNorm (q 0 + 1) 1) p := by
    have hq : ContDiffAt ℝ 2 (fun q : ConnectionParameters => q 0 + 1) p := by fun_prop
    apply ((hq.pow 2).add contDiffAt_const).sqrt
    positivity
  exact (hleft.sub hright).add contDiffAt_const

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

private theorem BianchiIX.hasFDerivAt_connectionEntrancePhase (p : ConnectionParameters) :
    HasFDerivAt (fun q : ConnectionParameters => phaseNorm (q 0 + 1) 1)
      (((p 0 + 1) / phaseNorm (p 0 + 1) 1) •
        (ContinuousLinearMap.proj (0 : Fin 3) : ConnectionParameters →L[ℝ] ℝ)) p := by
  have ha := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p).add_const 1
  have H := ((ha.pow 2).add_const 1).sqrt (by positivity : (p 0 + 1) ^ 2 + 1 ≠ 0)
  convert! H using 1
  · ext q
    simp [phaseNorm]
  · ext v
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
    simp only [phaseNorm, one_pow]
    ring

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

private theorem BianchiIX.connectionReturnPhysicalState_differential {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000)
    (v : ConnectionParameters) :
    let d := fderiv ℝ connectionReturnPhysicalState p v
    let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p v
    d 0 = ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 + fderiv ℝ connectionReturnPhaseError p v ∧
      d 1 = connectionReturnState p 1 * J 1 ∧ d 2 = connectionReturnState p 2 * J 2 := by
  intro d J
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0 := ⟨hu.1.le, hu.2⟩
  have hphys := (contDiffAt_connectionReturnPhysicalState hμ hu' hw).differentiableAt (by norm_num)
  have hstate := (connectionReturn_regular hμ hu' hw).2.2.1.differentiableAt (by norm_num)
  have herror := (contDiffAt_connectionReturnPhaseError hμ hu' hw).differentiableAt (by norm_num)
  have hphase : (fun q => connectionReturnPhysicalState q 0) =
      (fun q => phaseNorm (q 0 + 1) 1 - 2 + connectionReturnPhaseError q) := by
    ext q
    dsimp [connectionReturnPhysicalState, connectionReturnPhaseError]
    ring
  have hraw : d 0 = ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 + fderiv ℝ connectionReturnPhaseError p v := by
    have Hd := congrArg (fun A : ConnectionParameters →L[ℝ] ℝ => A v)
      (((hasFDerivAt_connectionEntrancePhase p).sub_const 2).add herror.hasFDerivAt).fderiv
    change fderiv ℝ (fun q => phaseNorm (q 0 + 1) 1 - 2 + connectionReturnPhaseError q) p v = _ at Hd
    rw [← hphase, fderiv_apply hphys 0] at Hd
    exact Hd
  have hc := connectionReturn_control hμ hu' hw
  have hr := (hc.2 (connectionReturnTime p) ⟨hc.1.le, le_rfl⟩).2
  change connectionRegion (p 0) (connectionReturnState p) at hr
  have hm : 1 < -connectionReturnState p 0 := by linarith only [hμ, (abs_le.mp hr.1).1]
  have hpos := connectionReturn_wall_pos hμ hu' hw
  have hU := ne_of_gt (hpos.2 hu.1)
  have hV := ne_of_gt hpos.1
  have hW : connectionReturnState p 3 ≠ 0 := by
    rw [(connectionReturn_growing_component hμ hu' hw).1]
    norm_num
  have hJ : J = connectionLogTangent (connectionReturnState p) (fderiv ℝ connectionReturnState p v) := by
    dsimp [J]
    rw [fderiv_comp p ((contDiffAt_connectionLogCoordinates 1 hm hU hV hW).differentiableAt (by norm_num)) hstate,
      ContinuousLinearMap.comp_apply, connectionLogCoordinates_fderiv hm hU hV hW]
  have hcomponent (i : Fin 2) : d i.succ = fderiv ℝ connectionReturnState p v i.succ.castSucc := by
    have heq : (fun q => connectionReturnPhysicalState q i.succ) = (fun q => connectionReturnState q i.succ.castSucc) := by
      ext q
      fin_cases i <;> rfl
    have HH := congrArg (fun f : ConnectionParameters → ℝ => fderiv ℝ f p) heq
    rw [fderiv_apply hphys i.succ, fderiv_apply hstate i.succ.castSucc] at HH
    exact congrArg (fun A : ConnectionParameters →L[ℝ] ℝ => A v)
      HH
  refine ⟨hraw, ?_, ?_⟩
  · have Hc : d 1 = fderiv ℝ connectionReturnState p v 1 := hcomponent 0
    rw [Hc, hJ]
    change _ = connectionReturnState p 1 * (_ / connectionReturnState p 1)
    field_simp
  · have Hc : d 2 = fderiv ℝ connectionReturnState p v 2 := hcomponent 1
    rw [Hc, hJ]
    change _ = connectionReturnState p 2 * (_ / connectionReturnState p 2)
    field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreExitConnectionParameters_phase {Z : CoreAngleState} (hK : 1 < Z 0) :
    phaseNorm (coreExitConnectionParameters Z 0 + 1) 1 = Z 0 := by
  have hs := Real.sq_sqrt (by nlinarith only [hK] : 0 ≤ Z 0 ^ 2 - 1)
  change Real.sqrt ((Real.sqrt (Z 0 ^ 2 - 1) - 1 + 1) ^ 2 + 1 ^ 2) = Z 0
  rw [show (Real.sqrt (Z 0 ^ 2 - 1) - 1 + 1) ^ 2 + 1 ^ 2 = Z 0 ^ 2 by nlinarith only [hs]]
  exact Real.sqrt_sq (by linarith only [hK])

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
open Set Filter
open scoped Topology

private theorem BianchiIX.coreExitConnectionParameters_differential {Z : CoreAngleState} (hK : 1 < Z 0)
    (v : CoreAngleState) :
    let p := coreExitConnectionParameters Z
    let w := fderiv ℝ coreExitConnectionParameters Z v
    ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * w 0 = v 0 ∧ w 1 = v 1 ∧ w 2 = v 2 := by
  intro p w
  have hc := (contDiffAt_coreExitConnectionParameters 1 hK).differentiableAt (by norm_num)
  have heq : (fun X => phaseNorm (coreExitConnectionParameters X 0 + 1) 1) =ᶠ[𝓝 Z]
      (fun X : CoreAngleState => X 0) := by
    filter_upwards [(continuous_apply 0).continuousAt.eventually (lt_mem_nhds hK)] with X hX
    exact coreExitConnectionParameters_phase hX
  have H := (hasFDerivAt_connectionEntrancePhase p).comp Z hc.hasFDerivAt
  have He := (H.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) Z)
  have Hphase := congrArg (fun A : CoreAngleState →L[ℝ] ℝ => A v) He
  have hcomponent (i : Fin 2) : w i.succ = v i.succ := by
    have Hi : HasFDerivAt (fun X => coreExitConnectionParameters X i.succ)
        (ContinuousLinearMap.proj i.succ : CoreAngleState →L[ℝ] ℝ) Z := by
      fin_cases i <;> exact hasFDerivAt_apply _ _
    have Hd := Hi.fderiv
    rw [fderiv_apply hc i.succ] at Hd
    exact congrArg (fun A : CoreAngleState →L[ℝ] ℝ => A v) Hd
  exact ⟨Hphase, hcomponent 0, hcomponent 1⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connectionEntry_coreExitParameters (Y : CoreAngleState) :
    connectionEntry (coreExitConnectionParameters Y 0) (coreExitConnectionParameters Y 1)
      (coreExitConnectionParameters Y 2) = coreTailEntry Y := by
  ext i
  fin_cases i <;> simp [connectionEntry, coreExitConnectionParameters, coreTailEntry, neg_sub]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connectionReturnState_coreExitParameters (Y : CoreAngleState) :
    connectionReturnState (coreExitConnectionParameters Y) =
      projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y) := by
  unfold connectionReturnState connectionInitialState
  rw [connectionEntry_coreExitParameters]
  rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreExitConnectionParameters_unit_phase {Y v : CoreAngleState} (hR : 1 < Y 0) (hv : v 0 = 1) :
    let p := coreExitConnectionParameters Y
    let w := fderiv ℝ coreExitConnectionParameters Y v
    ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * w 0 = 1 ∧ w 1 = v 1 ∧ w 2 = v 2 := by
  simpa only [hv] using coreExitConnectionParameters_differential hR v

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreExitConnectionParameters_long_range {Y : CoreAngleState} (hR : 11 / 2 ≤ Y 0) :
    4 ≤ coreExitConnectionParameters Y 0 ∧ Y 0 / 2 ≤ coreExitConnectionParameters Y 0 ∧
      coreExitConnectionParameters Y 0 < Y 0 := by
  have hsq := Real.sq_sqrt (by nlinarith only [hR] : 0 ≤ Y 0 ^ 2 - 1)
  have hs := Real.sqrt_nonneg (Y 0 ^ 2 - 1)
  change 4 ≤ Real.sqrt (Y 0 ^ 2 - 1) - 1 ∧ Y 0 / 2 ≤ Real.sqrt (Y 0 ^ 2 - 1) - 1 ∧
    Real.sqrt (Y 0 ^ 2 - 1) - 1 < Y 0
  refine ⟨?_, ?_, ?_⟩
  · nlinarith only [hsq, hs, hR, sq_nonneg (Y 0 - 11 / 2)]
  · have hnear : Y 0 - 1 ≤ Real.sqrt (Y 0 ^ 2 - 1) := by nlinarith only [hsq, hs, hR]
    linarith only [hnear, hR]
  · nlinarith only [hsq, hs, hR]

end
end


/-- Long reflection estimates in the physical radius, for the canonical first arrival. -/
theorem solution :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ Y : CoreAngleState,
      11 / 2 ≤ Y 0 → (0 < Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 < Y 2 ∧ Y 2 ≤ ε / Y 0) →
      IsLeast {t : ℝ | 0 < t ∧ projectiveOriginalFlow (coreTailEntry Y) 0 t 3 = 1}
        (reflectionReturnTime Y) ∧
      coreRadiusEntry (reflectionReturnState Y) =
        projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y)) ∧
      ContDiffAt ℝ 2 reflectionReturnTime Y ∧ ContDiffAt ℝ 2 reflectionReturnState Y ∧
      |reflectionReturnState Y 0 - (Y 0 - 2)| ≤ 300000 * (Y 1 + Y 2) / Y 0 ∧
      (∀ i : Fin 2, 0 < reflectionReturnState Y i.succ ∧ reflectionReturnState Y i.succ ≤ Y i.succ) ∧
      ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let d := fderiv ℝ reflectionReturnState Y v
        1 / 2 ≤ d 0 ∧ |d 0 - 1| ≤ 300000 * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
          ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (reflectionReturnState Y i.succ) * d 0 := by
  obtain ⟨ε, hε, hεmax, hsε, hεL⟩ := exists_connection_cone_threshold
  refine ⟨ε, hε, hεmax, ?_⟩
  intro Y hR hu hw
  let p := coreExitConnectionParameters Y
  obtain ⟨hμ, hRμ, hμR⟩ := coreExitConnectionParameters_long_range hR
  have hR0 : 0 < Y 0 := by linarith only [hR]
  have hR1 : 1 < Y 0 := by linarith only [hR]
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hup : 0 < p 1 ∧ p 1 ≤ ε / p 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_left hε.le hμ0 hμR.le)⟩
  have hwp : 0 < p 2 ∧ p 2 ≤ ε :=
    ⟨hw.1, hw.2.trans (div_le_self hε.le (by linarith only [hR]))⟩
  have hu' : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0 :=
    ⟨hup.1, hup.2.trans (div_le_div_of_nonneg_right hεmax hμ0.le)⟩
  have hw' : 0 < p 2 ∧ p 2 ≤ 1 / 10000 := ⟨hwp.1, hwp.2.trans hεmax⟩
  have HR := connectionReturn_regular hμ ⟨hu'.1.le, hu'.2⟩ hw'
  have hP := contDiffAt_coreExitConnectionParameters 2 hR1
  have hphys := contDiffAt_connectionReturnPhysicalState hμ ⟨hu'.1.le, hu'.2⟩ hw'
  have hx : connectionInitialState p = fromProjectiveState (coreTailEntry Y) := by
    dsimp only [connectionInitialState, p]
    rw [connectionEntry_coreExitParameters]
  have hden := connection_entry_denom_pos hμ ⟨hu'.1.le, hu'.2⟩ hw'
  have hdom (t : ℝ) (ht : 0 ≤ t) : t ∈ normalizedMaxDomain (connectionInitialState p) 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint (fromProjectiveState_constraint hden.ne') 0 ht
  have hfirst : IsLeast {t : ℝ | 0 < t ∧ projectiveOriginalFlow (coreTailEntry Y) 0 t 3 = 1}
      (reflectionReturnTime Y) := by
    refine ⟨⟨HR.1.1.1.1, ?_⟩, ?_⟩
    · have H := HR.1.1.1.2.2
      change connectionReturnState p 3 = 1 at H
      rwa [connectionReturnState_coreExitParameters] at H
    · intro t ht
      apply HR.1.1.2
      refine ⟨ht.1, hdom t ht.1.le, ?_⟩
      rw [hx]
      exact ht.2
  obtain ⟨_, _, _, _, _, hactual⟩ := connectionReturn_restart_bounds hμ hu' hw'
  rw [connectionReturnState_coreExitParameters] at hactual
  have hpos := connectionReturn_wall_pos hμ ⟨hu'.1.le, hu'.2⟩ hw'
  have hdec := connectionReturn_exponential_decay hμ hu' hw'
  have hw1 : p 2 ≤ 1 := hw'.2.trans (by norm_num)
  have hL : 0 ≤ -Real.log (p 2) := neg_nonneg.mpr (Real.log_nonpos hw'.1.le hw1)
  have hU : connectionReturnState p 1 ≤ p 1 := hdec.1.trans (mul_le_of_le_one_right hu'.1.le
    (Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hμ0.le hL])))
  have hW : connectionReturnState p 2 ≤ p 2 := hdec.2.trans (mul_le_of_le_one_right hw'.1.le
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith only [hL]) hμ0.le)))
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1.le hw.1.le
  have hphase : |reflectionReturnState Y 0 - (Y 0 - 2)| ≤ 24 * (p 1 + p 2 ^ 2) / p 0 := by
    have H := connectionReturn_phase_bound hμ ⟨hu'.1.le, hu'.2⟩ hw'
    have heq : connectionReturnPhaseError p = reflectionReturnState Y 0 - (Y 0 - 2) := by
      dsimp only [connectionReturnPhaseError, reflectionReturnState, connectionReturnPhysicalState,
        Matrix.cons_val_zero]
      rw [coreExitConnectionParameters_phase hR1]
      ring
    rwa [heq] at H
  refine ⟨hfirst, hactual, HR.2.1.comp Y hP, hphys.comp Y hP, ?_, ?_, ?_⟩
  · apply hphase.trans
    have hw2 : p 2 ^ 2 ≤ p 2 := by nlinarith only [hw'.1.le, hw1]
    calc
      _ ≤ 24 * (Y 1 + Y 2) / p 0 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hw2) (by norm_num)) hμ0.le
      _ ≤ 24 * (Y 1 + Y 2) / (Y 0 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (half_pos hR0) hRμ
      _ = 48 * (Y 1 + Y 2) / Y 0 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hb) hR0.le
  · intro i
    fin_cases i
    · exact ⟨hpos.2 hu'.1, hU⟩
    · exact ⟨hpos.1, hW⟩
  · intro v hv0 hv1 hv2 d
    let w := fderiv ℝ coreExitConnectionParameters Y v
    obtain ⟨hw0, hwv1, hwv2⟩ := coreExitConnectionParameters_unit_phase hR1 hv0
    have hw1' : |w 1| ≤ Real.sqrt (p 1) := by dsimp only [w]; rw [hwv1]; exact hv1
    have hw2' : |w 2| ≤ Real.sqrt (p 2) := by dsimp only [w]; rw [hwv2]; exact hv2
    have hd : d = fderiv ℝ connectionReturnPhysicalState p w := by
      change fderiv ℝ (connectionReturnPhysicalState ∘ coreExitConnectionParameters) Y v = _
      rw [fderiv_comp Y (hphys.differentiableAt (by norm_num)) (hP.differentiableAt (by norm_num)),
        ContinuousLinearMap.comp_apply]
    obtain ⟨hmargin, _, hcone1, hcone2⟩ :=
      connectionReturn_unit_cone hμ ⟨hε, hεmax⟩ hsε hεL hup hwp hw0 hw1' hw2'
    have hdf := (connectionReturnPhysicalState_differential hμ hu' hw' w).1
    rw [hw0] at hdf
    have herr : |d 0 - 1| ≤ 150000 * Real.sqrt (Y 1 + Y 2) / p 0 := by
      rw [hd, hdf, add_sub_cancel_left]
      exact connectionReturn_phase_cone_amplitude hμ hu' hw' hw0 hw1' hw2'
    refine ⟨by rw [hd]; linarith only [hmargin], herr.trans ?_, ?_⟩
    · calc
        _ ≤ 150000 * Real.sqrt (Y 1 + Y 2) / (Y 0 / 2) :=
          div_le_div_of_nonneg_left (by positivity) (half_pos hR0) hRμ
        _ = _ := by ring
    · intro i
      rw [hd]
      have hd0 : 0 ≤ fderiv ℝ connectionReturnPhysicalState p w 0 := by linarith only [hmargin]
      have hweak : 1 - (1 - Real.exp (-(-Real.log (p 2)) / (2 * p 0))) / 2 ≤ 1 := by
        have Hexp := Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) (by positivity : 0 ≤ 2 * p 0))
        linarith only [Hexp]
      fin_cases i
      · change |fderiv ℝ connectionReturnPhysicalState p w 1| ≤
          Real.sqrt (connectionReturnState p 1) * fderiv ℝ connectionReturnPhysicalState p w 0
        exact hcone1.trans (by
          simpa only [one_mul] using! mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) / 3 ≤ 1)
              (Real.sqrt_nonneg (connectionReturnState p 1))) hd0)
      · change |fderiv ℝ connectionReturnPhysicalState p w 2| ≤
          Real.sqrt (connectionReturnState p 2) * fderiv ℝ connectionReturnPhysicalState p w 0
        exact hcone2.trans (by
          simpa only [one_mul] using! mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hweak (Real.sqrt_nonneg (connectionReturnState p 2))) hd0)
