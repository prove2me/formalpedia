-- Prove2me | solution 1 for BianchiIX.exists_partialCoreDownwardConnection_phase_error
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:39:52.7913+00:00
-- url     : https://prove2.me/submissions/98aab614-2646-4d7d-9640-6f3f908ecf8b

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturnValues
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Theorems.Thm_BianchiIX_connectionLog_matchingPhase_drift
import Theorems.Thm_BianchiIX_connectionLog_prefix_estimates
import Theorems.Thm_BianchiIX_connectionReturn_phase_response_bounds
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_connection_phase_composition_bounds
import Theorems.Thm_BianchiIX_connection_phase_radial_budget
import Theorems.Thm_BianchiIX_connection_reciprocal_radial_bounds
import Theorems.Thm_BianchiIX_exists_connection_first_return
import Theorems.Thm_BianchiIX_exists_normalized_connection_log_segment
import Theorems.Thm_BianchiIX_exists_partialCore_downward_radius_response
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Theorems.Thm_BianchiIX_partialCoreDownwardReturn_connection_domain
import Theorems.Thm_BianchiIX_partialCoreDownwardReturn_radial_multipliers
import Theorems.Thm_BianchiIX_partialCoreDownwardReturn_radial_response
import Theorems.Thm_BianchiIX_partial_core_connection_wall_budget
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.three_coordinate_expansion (v : Fin 3 → ℝ) :
    v = v 0 • ![1, 0, 0] + v 1 • ![0, 1, 0] + v 2 • ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.three_coordinate_linear_bound (A : (Fin 3 → ℝ) →L[ℝ] ℝ) (v : Fin 3 → ℝ) :
    |A v| ≤ |v 0| * |A ![1, 0, 0]| + |v 1| * |A ![0, 1, 0]| + |v 2| * |A ![0, 0, 1]| := by
  have hid : A v = v 0 * A ![1, 0, 0] + v 1 * A ![0, 1, 0] + v 2 * A ![0, 0, 1] := by
    conv_lhs => rw [three_coordinate_expansion v]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hid]
  simpa only [abs_mul] using
    (abs_add_le (v 0 * A ![1, 0, 0] + v 1 * A ![0, 1, 0]) (v 2 * A ![0, 0, 1])).trans
      (add_le_add (abs_add_le (v 0 * A ![1, 0, 0]) (v 1 * A ![0, 1, 0])) le_rfl)

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

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

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

private theorem BianchiIX.phaseNorm_ratio_bounds {a b : ℝ} (ha : 2 ≤ a) (hb : 0 ≤ b ∧ b ≤ 1) :
    7 / 8 ≤ a / phaseNorm a b ∧ a / phaseNorm a b ≤ 1 := by
  have ha0 : 0 < a := by linarith only [ha]
  have hn := phaseNorm_pos (b := b) ha0
  have hb2 : b ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hb.1 hb.2 2
  have ha2 : 4 ≤ a ^ 2 := by nlinarith only [ha, sq_nonneg (a - 2)]
  have hupper : phaseNorm a b ≤ 8 * a / 7 := by
    nlinarith only [phaseNorm_sq a b, hb2, ha2, hn, ha0]
  exact ⟨(le_div_iff₀ hn).mpr (by linarith only [hupper]),
    (div_le_one hn).mpr (phaseNorm_ge ha0.le)⟩

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
open Filter
open scoped Topology

private theorem BianchiIX.connectionReturn_phase_response_bounds_nonneg {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    |fderiv ℝ connectionReturnPhaseError p ![1, 0, 0]| ≤ 50000 * (p 1 + (p 2) ^ 2) / (p 0) ^ 2 ∧
    |fderiv ℝ connectionReturnPhaseError p ![0, 1, 0]| ≤ 50000 / p 0 ∧
    |fderiv ℝ connectionReturnPhaseError p ![0, 0, 1]| ≤ 50000 * (p 1 + p 2) / p 0 := by
  by_cases hpos : 0 < p 1
  · exact connectionReturn_phase_response_bounds hμ ⟨hpos, hu.2⟩ hw
  have hp1 : p 1 = 0 := le_antisymm (le_of_not_gt hpos) hu.1
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  let ε : ℝ := (1 / 10000) / p 0
  have hε : 0 < ε := by dsimp [ε]; positivity
  let q : ℕ → ConnectionParameters := fun n => ![p 0, ε / ((n : ℝ) + 1), p 2]
  have hqU (n : ℕ) : 0 < q n 1 ∧ q n 1 ≤ (1 / 10000) / q n 0 := by
    change 0 < ε / ((n : ℝ) + 1) ∧ ε / ((n : ℝ) + 1) ≤ ε
    exact ⟨div_pos hε (by positivity), div_le_self hε.le (by have H : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith only [H])⟩
  have hq : Tendsto q atTop (𝓝 p) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · have H := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
      simpa [q, hp1, div_eq_mul_inv] using H
    · exact tendsto_const_nhds
  have H (n : ℕ) := connectionReturn_phase_response_bounds (p := q n) hμ (hqU n) hw
  have hd (v : ConnectionParameters) : ContinuousAt (fun r => |fderiv ℝ connectionReturnPhaseError r v|) p :=
    (((contDiffAt_connectionReturnPhaseError hμ hu hw).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).abs
  have hRμ : ContinuousAt (fun r : ConnectionParameters => 50000 * (r 1 + (r 2) ^ 2) / (r 0) ^ 2) p := by
    fun_prop (disch := exact pow_ne_zero 2 hμne)
  have hRU : ContinuousAt (fun r : ConnectionParameters => 50000 / r 0) p := by
    exact continuousAt_const.div (continuous_apply (0 : Fin 3)).continuousAt hμne
  have hRW : ContinuousAt (fun r : ConnectionParameters => 50000 * (r 1 + r 2) / r 0) p := by
    fun_prop (disch := exact hμne)
  exact ⟨le_of_tendsto_of_tendsto' ((hd ![1, 0, 0]).tendsto.comp hq) (hRμ.tendsto.comp hq) (fun n => (H n).1),
    le_of_tendsto_of_tendsto' ((hd ![0, 1, 0]).tendsto.comp hq) (hRU.tendsto.comp hq) (fun n => (H n).2.1),
    le_of_tendsto_of_tendsto' ((hd ![0, 0, 1]).tendsto.comp hq) (hRW.tendsto.comp hq) (fun n => (H n).2.2)⟩

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

private theorem BianchiIX.connectionReturn_phase_curve_bounds {p : ℝ → ConnectionParameters}
    {v : ConnectionParameters} {x r K M A B U P : ℝ}
    (hp : HasDerivAt p v x) (hr : 0 < r) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hμ : 4 ≤ p x 0) (hi : 1 / p x 0 ≤ K * r)
    (hu : 0 ≤ p x 1 ∧ p x 1 ≤ (1 / 10000) / p x 0)
    (hw : 0 < p x 2 ∧ p x 2 ≤ 1 / 10000)
    (hU : 0 ≤ U) (hP : 0 ≤ P ∧ P ≤ 1) (huU : p x 1 ≤ U) (hwP : p x 2 ≤ P)
    (hv0 : |v 0| ≤ M / r ^ 2) (hv1 : r * |v 1| ≤ A * U) (hv2 : r * |v 2| ≤ B * P) :
    DifferentiableAt ℝ (fun a => connectionReturnPhaseError (p a)) x ∧
      |connectionReturnPhaseError (p x)| ≤ 24 * K * r * (U + P ^ 2) ∧
      |deriv (fun a => connectionReturnPhaseError (p a)) x| ≤
        50000 * (K ^ 2 * M + K * A + K * B) * (U + P ^ 2) := by
  have hw0 := hw.1.le
  have Hreg := (contDiffAt_connectionReturnPhaseError hμ hu hw).differentiableAt (by norm_num)
  have HD := Hreg.hasFDerivAt.comp_hasDerivAt (f := p) x hp
  dsimp only [Function.comp_def] at HD
  have Hcols := connectionReturn_phase_response_bounds_nonneg hμ hu hw
  have Hlinear := three_coordinate_linear_bound (fderiv ℝ connectionReturnPhaseError (p x)) v
  have Hbound := Hlinear.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left Hcols.1 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left Hcols.2.1 (abs_nonneg _)))
    (mul_le_mul_of_nonneg_left Hcols.2.2 (abs_nonneg _)))
  refine ⟨HD.differentiableAt, ?_, ?_⟩
  · calc
      _ ≤ 24 * (p x 1 + (p x 2) ^ 2) / p x 0 := connectionReturn_phase_bound hμ hu hw
      _ = 24 * (p x 1 + (p x 2) ^ 2) * (1 / p x 0) := by ring
      _ ≤ 24 * (U + P ^ 2) * (K * r) := by gcongr
      _ = _ := by ring
  · rw [HD.deriv]
    exact Hbound.trans (connection_phase_radial_budget hr hK hM hA hB
      (by linarith only [hμ]) hi hU hP ⟨hu.1, huU⟩ ⟨hw.1.le, hwP⟩ hv0 hv1 hv2)

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

private theorem BianchiIX.partialCoreDownwardReturn_connectionParameters_eventuallyEq {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    let out := fun z => projectiveOriginalFlow z 0 (partialCoreDownwardReturnTime z)
    (fun z => coreExitConnectionParameters ![coreRadius (out z 0) (out z 2), out z 1, out z 3]) =ᶠ[𝓝 y]
      (fun z => coreExitConnectionParameters (partialCoreDownwardReturnState z)) := by
  intro out
  filter_upwards [(partialCoreDownwardReturn_regular hk hy hR hV).2.2.2.1] with z hz
  have hhit : out z 2 = 1 := hz.1.1.2.2.1
  apply congrArg coreExitConnectionParameters
  ext i
  fin_cases i
  · rfl
  · rfl
  · change out z 3 = out z 2 * out z 3
    rw [hhit, one_mul]

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


/-- Uniform E.28 for a radial curve through the fixed downward return, including its incoming boundary. -/
theorem solution {K : ℝ} (hK : 1 ≤ K) :
    ∃ C > (0 : ℝ), ∀ {Y : ℝ → ProjectiveState} {x r Z : ℝ},
      (0 < r ∧ r ≤ 1) → 0 ≤ Z → DifferentiableAt ℝ Y x →
      let k := fun a => coreRadius (Y a 0) (Y a 2)
      let U := Y x 1
      let W := Y x 2 * Y x 3
      let z := fun a => projectiveCoreAngle (Y a)
      let τ := partialCoreDownwardReturnTime
      let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
      let f := fun a => coreRadius (out a 0) (out a 2)
      let p := fun a => coreExitConnectionParameters ![f a, out a 1, out a 3]
      let Δ := fun a => connectionReturnPhaseError (p a)
      let g := fun a => connectionReturnPhysicalState (p a) 0
      let E := 16 * K + 4 * (4096 * coreVariationBound) * K ^ 2 + C
      let R := fun a => 2 / g a - (2 / k a) / (1 - 2 / k a)
      6 ≤ k x → coreRegion (k x) (Y x) → (1 < Y x 2 ∨ (Y x 2 = 1 ∧ 1 ≤ Y x 0)) →
      2 * Real.cosh Z ≤ k x → z x ≤ Z → 0 < U → 0 < W →
      2 / (K * r) ≤ k x → k x ≤ K / r → |deriv k x| ≤ K / r ^ 2 →
      |deriv (fun a => Y a 1) x| ≤ K * U / r →
      |deriv (fun a => Y a 2 * Y a 3) x| ≤ K * W / r → |deriv z x| ≤ K / r →
      connectionReturnValid (p x) ∧
      connectionReturnState (p x) = projectiveOriginalFlow (Y x) 0 (τ (Y x) + connectionReturnTime (p x)) ∧
      DifferentiableAt ℝ k x ∧ DifferentiableAt ℝ f x ∧
      |f x - k x| ≤ 16 * K * (U + r * W ^ 2) ∧
      |deriv (fun a => f a - k a) x| ≤ 4 * (4096 * coreVariationBound) * K ^ 2 * (U + r * W) / r ^ 2 ∧
      DifferentiableAt ℝ Δ x ∧ |Δ x| ≤ C * r * (U + W ^ 2) ∧ |deriv Δ x| ≤ C * (U + W ^ 2) ∧
      DifferentiableAt ℝ g x ∧ k x / 4 ≤ g x ∧
      DifferentiableAt ℝ R x ∧ |R x| ≤ 8 * E * K ^ 2 * r ^ 2 * (U + r * W ^ 2) ∧
      |deriv R x| ≤ (8 * E * K ^ 2 + 32 * E * K ^ 4) * (U + r * W) := by
  let A := (200 * coreVariationBound + 2) * K ^ 2
  let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
  let F := K + 8 * (4096 * coreVariationBound) * K ^ 2
  let CU := K * (1 + 576 * A)
  let CW := K * (1 + B)
  let C := 1 + 24 * K + 50000 * (K ^ 2 * (2 * F) + K * CU + K * CW)
  have hK0 : 0 < K := by linarith only [hK]
  have hA : 0 ≤ A := by dsimp only [A, coreVariationBound]; positivity
  have hB : 0 ≤ B := by dsimp only [B, coreVariationBound]; positivity
  have hF : 0 ≤ F := by dsimp only [F, coreVariationBound]; positivity
  have hCU : 0 ≤ CU := by dsimp only [CU]; positivity
  have hCW : 0 ≤ CW := by dsimp only [CW]; positivity
  have hcoef : 0 ≤ 50000 * (K ^ 2 * (2 * F) + K * CU + K * CW) := by positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Y x r Z hr hZ hY k U W z τ out f p Δ g E R hk hy hV hkZ hz hUpos hWpos hklo hkhi hdk hdU hdW hdz
  have hr0 := hr.1
  have hk0 : 0 < k x := by linarith only [hk]
  have hU : 0 ≤ U := hy.2.2.1.1
  have hW : 0 ≤ W ∧ W ≤ 1 :=
    ⟨hy.2.2.2.1, (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)⟩
  have hU1 : U ≤ 1 := (coreBootstrap_wall_bound hk hy.2.2.1.2).trans (by norm_num)
  have hki : 1 / k x ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [(div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo]
  obtain ⟨hf, _, _, _, hfval, hfder, _⟩ := partialCoreDownwardReturn_radial_response hr hK hY
    hk hy hV hklo hkhi hdk hdU hdW hdz
  obtain ⟨_, _, _, _, _, hu, hw, hu0, hw0, hdu, hdw, _⟩ :=
    partialCoreDownwardReturn_radial_multipliers hr hK hY hk hy hV hki hkhi hdk hdU hdW hdz
  obtain ⟨_, hμ, huε, hwε, hdecU, hdecW, hphase, _, hvalid, _, _, horbit⟩ :=
    partialCoreDownwardReturn_connection_domain hk hy rfl hV hZ hkZ hz
      ⟨by norm_num, le_rfl⟩ ⟨hUpos, hy.2.2.1.2⟩ ⟨hWpos, hy.2.2.2.2⟩
  let u := fun a => out a 1
  let w := fun a => out a 3
  have hp : p x = coreExitConnectionParameters (partialCoreDownwardReturnState (Y x)) :=
    (partialCoreDownwardReturn_connectionParameters_eventuallyEq hk hy rfl hV).self_of_nhds
  rw [← hp] at hμ huε hwε hdecU hdecW hphase hvalid horbit
  have hphase' : phaseNorm (p x 0 + 1) 1 = f x := hphase
  have hf1 : 1 < f x := by
    have Hb := phaseNorm_ge (b := 1) (show 0 ≤ p x 0 + 1 by linarith only [hμ.1])
    rw [hphase'] at Hb
    linarith only [hμ.1, Hb]
  have hkd : DifferentiableAt ℝ k x := by
    have H := ((contDiffAt_toCoreAngleState 1 (zero_lt_one.trans_le hy.2.1)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
    exact (hasDerivAt_pi.mp H 0).differentiableAt
  change DifferentiableAt ℝ f x at hf
  change |deriv (fun a => f a - k a) x| ≤
    4 * (4096 * coreVariationBound) * K ^ 2 * (U + r * W) / r ^ 2 at hfder
  have hfhi : |deriv f x| ≤ F / r ^ 2 := by
    have hs : U + r * W ≤ 2 := by nlinarith only [hU1, mul_le_mul hr.2 hW.2 hW.1 (by norm_num : (0 : ℝ) ≤ 1)]
    have He := hfder.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (by dsimp only [coreVariationBound]; positivity)) (sq_nonneg r))
    rw [deriv_fun_sub hf hkd] at He
    calc
      _ = |deriv k x + (deriv f x - deriv k x)| := by congr 1; ring
      _ ≤ |deriv k x| + |deriv f x - deriv k x| := abs_add_le _ _
      _ ≤ K / r ^ 2 + 4 * (4096 * coreVariationBound) * K ^ 2 * 2 / r ^ 2 := add_le_add hdk He
      _ = _ := by dsimp only [F]; ring
  have Hwall := partial_core_connection_wall_budget hr.1 hK0.le hk hki hkhi hA hB hU hu0 hw0 hdecU hdecW hdu hdw
  let v : CoreAngleState := ![deriv f x, deriv u x, deriv w x]
  have hcurve : HasDerivAt (fun a => ![f a, u a, w a]) v x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hf.hasDerivAt
    · exact hu.hasDerivAt
    · exact hw.hasDerivAt
  let ξ := fderiv ℝ coreExitConnectionParameters ![f x, u x, w x] v
  have Hp : HasDerivAt p ξ x := ((contDiffAt_coreExitConnectionParameters 1 hf1).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt (f := fun a => ![f a, u a, w a]) x hcurve
  have Hξ := coreExitConnectionParameters_differential (Z := ![f x, u x, w x]) hf1 v
  change ((p x 0 + 1) / phaseNorm (p x 0 + 1) 1) * ξ 0 = deriv f x ∧
    ξ 1 = deriv u x ∧ ξ 2 = deriv w x at Hξ
  have hμi : 1 / p x 0 ≤ K * r := by
    apply (div_le_iff₀ (by linarith only [hμ.1] : 0 < p x 0)).mpr
    have H := (div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo
    have H' := mul_le_mul_of_nonneg_right hμ.2.1 (mul_pos hK0 hr.1).le
    nlinarith only [H, H']
  have hξ0 : |ξ 0| ≤ 2 * |deriv f x| := by
    let L := (p x 0 + 1) / phaseNorm (p x 0 + 1) 1
    have HL := (phaseNorm_ratio_bounds (b := 1) (by linarith only [hμ.1] : 2 ≤ p x 0 + 1) (by norm_num)).1
    have HL0 : 0 ≤ L := by dsimp only [L]; linarith only [HL]
    have HE : L * |ξ 0| = |deriv f x| := by rw [← Hξ.1, abs_mul, abs_of_nonneg HL0]
    nlinarith only [mul_le_mul_of_nonneg_right HL (abs_nonneg (ξ 0)), HE, abs_nonneg (ξ 0)]
  have HΔ := connectionReturn_phase_curve_bounds Hp hr.1 hK0.le (by positivity : 0 ≤ 2 * F) hCU hCW
    hμ.1 hμi ⟨huε.1.le, huε.2⟩ hwε hU hW Hwall.1 hdecW
    (hξ0.trans ((mul_le_mul_of_nonneg_left hfhi (by norm_num)).trans_eq (by ring)))
    (by rw [Hξ.2.1]; exact Hwall.2.1) (by rw [Hξ.2.2]; exact Hwall.2.2)
  have hΔval : |Δ x| ≤ C * r * (U + W ^ 2) :=
    HΔ.2.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show 24 * K ≤ C by dsimp only [C]; linarith only [hcoef]) hr.1.le)
      (by positivity))
  have hΔder : |deriv Δ x| ≤ C * (U + W ^ 2) :=
    HΔ.2.2.trans (mul_le_mul_of_nonneg_right
      (show 50000 * (K ^ 2 * (2 * F) + K * CU + K * CW) ≤ C by dsimp only [C]; linarith only [hK0])
      (by positivity))
  have hE : 0 ≤ E := by dsimp only [E, coreVariationBound]; positivity
  have Hgerm : g =ᶠ[𝓝 x] (fun a => f a - 2 + Δ a) := by
    filter_upwards [hf.continuousAt.eventually (lt_mem_nhds hf1)] with a ha
    have Hphase := coreExitConnectionParameters_phase (Z := ![f a, u a, w a]) ha
    change phaseNorm (p a 0 + 1) 1 = f a at Hphase
    dsimp only [g, Δ, connectionReturnPhysicalState, connectionReturnPhaseError]
    simp only [Matrix.cons_val_zero, Hphase]
    ring
  have hglo : k x / 4 ≤ g x := by
    have Hcontrol := connectionReturn_control hμ.1 ⟨huε.1.le, huε.2⟩ hwε
    have Hregion := (Hcontrol.2 (connectionReturnTime (p x)) ⟨Hcontrol.1.le, le_rfl⟩).2
    change connectionRegion (p x 0) (connectionReturnState (p x)) at Hregion
    have HM := (abs_le.mp Hregion.1).1
    have Hleft : p x 0 / 2 ≤ -connectionReturnState (p x) 0 - 1 := by linarith only [HM, hμ.1]
    have Hnorm := phaseNorm_ge (b := 1) (show 0 ≤ -connectionReturnState (p x) 0 - 1 by linarith only [Hleft, hμ.1])
    change _ ≤ g x at Hnorm
    linarith only [hμ.2.1, Hleft, Hnorm]
  have Hcomp := connection_phase_composition_bounds hr hU hW (by positivity : 0 ≤ 16 * K)
    (by dsimp only [coreVariationBound]; positivity : 0 ≤ 4 * (4096 * coreVariationBound) * K ^ 2)
    hC.le hf hkd HΔ.1 Hgerm hfval hfder hΔval hΔder
  have Hrec := connection_reciprocal_radial_bounds hr hK hE hU hW Hcomp.1 hkd hk hklo hglo hdk Hcomp.2.1 Hcomp.2.2
  exact ⟨hvalid, horbit, hkd, hf, hfval, hfder, HΔ.1, hΔval, hΔder, Hcomp.1, hglo, Hrec⟩
