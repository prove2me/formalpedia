-- Prove2me | solution 1 for BianchiIX.connectionReturn_unit_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T10:48:29.033984+00:00
-- url     : https://prove2.me/submissions/b0835d70-e37f-4925-9488-984d3c6caecb

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
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_ConnectionClockDifferential
import Definitions.Def_BianchiIX_Analysis_ConnectionLogCoordinates
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturnValues
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Theorems.Thm_BianchiIX_connectionLog_prefix_estimates
import Theorems.Thm_BianchiIX_connectionReturn_log_amplitude_bounds
import Theorems.Thm_BianchiIX_connectionReturn_phase_response_bounds
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_connection_strong_cone_size
import Theorems.Thm_BianchiIX_connection_weak_cone_size
import Theorems.Thm_BianchiIX_exists_connectionReturn_log_clock
import Theorems.Thm_BianchiIX_exists_connection_first_return
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Positivity

noncomputable section
open BianchiIX

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

private theorem BianchiIX.exp_neg_le_one_sub_half {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-x) ≤ 1 - x / 2 := by
  have hp : 0 < x + 1 := by linarith only [hx]
  rw [Real.exp_neg]
  calc
    _ ≤ (x + 1)⁻¹ := inv_le_inv₀ (Real.exp_pos _) hp |>.mpr (Real.add_one_le_exp x)
    _ ≤ 1 - x / 2 := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hp).mpr
      nlinarith only [mul_nonneg hx (sub_nonneg.mpr hx1)]

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

private theorem BianchiIX.sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos x).le (Real.exp_pos (x / 2)).le).mpr
  rw [← Real.exp_add, add_halves]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sqrt_le_sqrt_mul_exp_half {U u x : ℝ} (hu : 0 ≤ u) (hU : U ≤ u * Real.exp x) :
    Real.sqrt U ≤ Real.sqrt u * Real.exp (x / 2) := by
  simpa only [Real.sqrt_mul hu, sqrt_exp_half] using Real.sqrt_le_sqrt hU

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_cone_phase_size {μ ε u w : ℝ} (hμ : 4 ≤ μ) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ ε / μ) (hw : 0 ≤ w ∧ w ≤ ε) :
    2 * (u + w ^ 2) / μ + Real.sqrt u + (u + w) * Real.sqrt w ≤ 4 * Real.sqrt ε := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hue : u ≤ ε := hu.2.trans (div_le_self hε.1 (by linarith only [hμ]))
  have hsu := Real.sqrt_le_sqrt hue
  have hsw := Real.sqrt_le_sqrt hw.2
  have hse := Real.sqrt_nonneg ε
  have hes : ε ≤ Real.sqrt ε := by
    have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε.2
    nlinarith only [Real.sq_sqrt hε.1, hs1, hse]
  have hw2 : w ^ 2 ≤ ε := by nlinarith only [hw.1, hw.2, hε.2]
  have hfirst : 2 * (u + w ^ 2) / μ ≤ Real.sqrt ε := by
    apply (div_le_iff₀ hμ0).mpr
    have H := mul_le_mul_of_nonneg_right hμ hse
    nlinarith only [hue, hw2, hes, H]
  have hlast : (u + w) * Real.sqrt w ≤ 2 * Real.sqrt ε := by
    exact (mul_le_mul (show u + w ≤ 2 by linarith only [hue, hw.2, hε.2]) hsw
      (Real.sqrt_nonneg w) (by norm_num)).trans_eq (by ring)
  linarith only [hfirst, hsu, hlast]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_cone_gap {μ L : ℝ} (hμ : 4 ≤ μ) (hL : 4 ≤ L) :
    1 / μ ≤ 1 - Real.exp (-L / (2 * μ)) ∧ 1 - Real.exp (-L / (2 * μ)) ≤ 1 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hx : 0 ≤ 2 / μ := by positivity
  have hx1 : 2 / μ ≤ 1 := (div_le_one hμ0).mpr (by linarith only [hμ])
  have H := exp_neg_le_one_sub_half hx hx1
  have Hexp : Real.exp (-L / (2 * μ)) ≤ Real.exp (-(2 / μ)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ -4 / (2 * μ) := div_le_div_of_nonneg_right (neg_le_neg hL) (by positivity)
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · have heq : 2 / μ / 2 = 1 / μ := by ring
    rw [heq] at H
    linarith only [H, Hexp]
  · linarith only [Real.exp_pos (-L / (2 * μ))]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_cone_phase_margin {μ L d : ℝ} (hμ : 4 ≤ μ) (hL : 4 ≤ L)
    (hd : |d - 1| ≤ 1 / (4 * μ)) :
    3 / 4 ≤ d ∧
      1 / 4 ≤ (1 / 3) * d ∧
      Real.exp (-L / (2 * μ)) ≤ (1 - (1 - Real.exp (-L / (2 * μ))) / 2) * d := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  let γ := 1 - Real.exp (-L / (2 * μ))
  have hg := connection_cone_gap hμ hL
  have hg0 : 0 ≤ γ := (by positivity : (0 : ℝ) ≤ 1 / μ).trans hg.1
  have hsmall : 1 / (4 * μ) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * μ)).mpr
    linarith only [hμ]
  have hdlo := (abs_le.mp hd).1
  have hd3 : 3 / 4 ≤ d := by linarith only [hdlo, hsmall]
  have hdγ : 1 - γ / 4 ≤ d := by
    have heq : 1 / (4 * μ) = (1 / μ) / 4 := by ring
    rw [heq] at hdlo
    linarith only [hg.1, hdlo]
  refine ⟨hd3, by linarith only [hd3], ?_⟩
  have hfac : 0 ≤ 1 - γ / 2 := by linarith only [hg.2]
  have H := mul_le_mul_of_nonneg_left hdγ hfac
  have Hfinal : 1 - γ ≤ (1 - γ / 2) * d := by nlinarith only [H, hg0, sq_nonneg γ]
  dsimp only [γ] at Hfinal
  linarith only [Hfinal]

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

private theorem BianchiIX.connection_unit_phase_direction {p v : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hv : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1) : |v 0| ≤ 2 := by
  have H := phaseNorm_ratio_bounds (b := 1) (by linarith only [hμ] : 2 ≤ p 0 + 1) (by norm_num)
  have hR : 0 < (p 0 + 1) / phaseNorm (p 0 + 1) 1 := by linarith only [H.1]
  have hv0 : 0 ≤ v 0 := by nlinarith only [hv, hR]
  rw [abs_of_nonneg hv0]
  have HH := mul_le_mul_of_nonneg_right H.1 hv0
  nlinarith only [HH, hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionReturn_cone_direction_bounds {p v : ConnectionParameters} {ε : ℝ}
    (hμ : 4 ≤ p 0) (hε : 0 ≤ ε ∧ ε ≤ 1 / 10000)
    (hu : 0 < p 1 ∧ p 1 ≤ ε / p 0) (hw : 0 < p 2 ∧ p 2 ≤ ε)
    (hv : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1)
    (hvu : |v 1| ≤ Real.sqrt (p 1)) (hvw : |v 2| ≤ Real.sqrt (p 2)) :
    let L := -Real.log (p 2)
    let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p
    |fderiv ℝ connectionReturnPhaseError p v| ≤ 200000 * Real.sqrt ε / p 0 ∧
      |J v 1| ≤ 274 * L + 9000 * (1 / p 1 + L / p 0) * Real.sqrt (p 1) +
        32 * p 0 / p 2 * Real.sqrt (p 2) ∧
      |J v 2| ≤ 274 * L / p 0 ^ 2 + 9000 * (1 + L) / p 0 ^ 2 * Real.sqrt (p 1) +
        (1 + 32 / p 0) / p 2 * Real.sqrt (p 2) := by
  intro L J
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hu' : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right hε.2 hμ0.le)⟩
  have hw' : 0 < p 2 ∧ p 2 ≤ 1 / 10000 := ⟨hw.1, hw.2.trans hε.2⟩
  have hv0 := connection_unit_phase_direction hμ hv
  have H := connectionReturn_phase_response_bounds_nonneg hμ ⟨hu'.1.le, hu'.2⟩ hw'
  have HA := connectionReturn_log_amplitude_bounds hμ hu' hw'
  have hphase := three_coordinate_linear_bound (fderiv ℝ connectionReturnPhaseError p) v
  have H0 := mul_le_mul hv0 H.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have H1 := mul_le_mul hvu H.2.1 (abs_nonneg _) (Real.sqrt_nonneg _)
  have H2 := mul_le_mul hvw H.2.2 (abs_nonneg _) (Real.sqrt_nonneg _)
  have Hsize := connection_cone_phase_size hμ ⟨hε.1, by linarith only [hε.2]⟩ ⟨hu.1.le, hu.2⟩ ⟨hw.1.le, hw.2⟩
  have Hscaled := mul_le_mul_of_nonneg_left Hsize (show 0 ≤ 50000 / p 0 by positivity)
  have Hbound : |fderiv ℝ connectionReturnPhaseError p v| ≤
      (50000 / p 0) * (2 * (p 1 + p 2 ^ 2) / p 0 + Real.sqrt (p 1) +
        (p 1 + p 2) * Real.sqrt (p 2)) := by
    calc
      _ ≤ 2 * (50000 * (p 1 + p 2 ^ 2) / p 0 ^ 2) +
          Real.sqrt (p 1) * (50000 / p 0) + Real.sqrt (p 2) * (50000 * (p 1 + p 2) / p 0) :=
        hphase.trans (add_le_add (add_le_add H0 H1) H2)
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · exact (Hbound.trans Hscaled).trans_eq (by ring)
  · have Hb := three_coordinate_linear_bound
      ((ContinuousLinearMap.proj (1 : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ).comp J) v
    have Ha := mul_le_mul hv0 HA.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have Hc := mul_le_mul hvu HA.2.2.1 (abs_nonneg _) (Real.sqrt_nonneg _)
    have Hd := mul_le_mul hvw HA.2.2.2.2.1 (abs_nonneg _) (Real.sqrt_nonneg _)
    change |J v 1| ≤ |v 0| * |J ![1, 0, 0] 1| + |v 1| * |J ![0, 1, 0] 1| + |v 2| * |J ![0, 0, 1] 1| at Hb
    exact (Hb.trans (add_le_add (add_le_add Ha Hc) Hd)).trans_eq (by ring)
  · have Hb := three_coordinate_linear_bound
      ((ContinuousLinearMap.proj (2 : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ).comp J) v
    have Ha := mul_le_mul hv0 HA.2.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have Hc := mul_le_mul hvu HA.2.2.2.1 (abs_nonneg _) (Real.sqrt_nonneg _)
    have Hd := mul_le_mul hvw HA.2.2.2.2.2 (abs_nonneg _) (Real.sqrt_nonneg _)
    change |J v 2| ≤ |v 0| * |J ![1, 0, 0] 2| + |v 1| * |J ![0, 1, 0] 2| + |v 2| * |J ![0, 0, 1] 2| at Hb
    exact (Hb.trans (add_le_add (add_le_add Ha Hc) Hd)).trans_eq (by ring)

end
end

/-- The actual positive-wall connection preserves unit physical-phase cone directions,
with a uniform strong margin and the nonuniform weak margin of B.31. -/
theorem solution {p v : ConnectionParameters} {ε : ℝ}
    (hμ : 4 ≤ p 0) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hsε : Real.sqrt ε ≤ 1 / 1000000) (hεL : ε ≤ Real.exp (-256))
    (hu : 0 < p 1 ∧ p 1 ≤ ε / p 0) (hw : 0 < p 2 ∧ p 2 ≤ ε)
    (hv : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1)
    (hvu : |v 1| ≤ Real.sqrt (p 1)) (hvw : |v 2| ≤ Real.sqrt (p 2)) :
    let L := -Real.log (p 2)
    let d := fderiv ℝ connectionReturnPhysicalState p v
    3 / 4 ≤ d 0 ∧ |d 0 - 1| ≤ 1 / (4 * p 0) ∧
      |d 1| ≤ (1 / 3) * Real.sqrt (connectionReturnState p 1) * d 0 ∧
      |d 2| ≤ (1 - (1 - Real.exp (-L / (2 * p 0))) / 2) *
        Real.sqrt (connectionReturnState p 2) * d 0 := by
  intro L d
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hu' : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right hε.2 hμ0.le)⟩
  have hw' : 0 < p 2 ∧ p 2 ≤ 1 / 10000 := ⟨hw.1, hw.2.trans hε.2⟩
  have hL : 256 ≤ L := by
    have H := Real.log_le_log hw.1 (hw.2.trans hεL)
    rw [Real.log_exp] at H
    linarith only [H]
  have hwexp : p 2 = Real.exp (-L) := by simp only [L, neg_neg, Real.exp_log hw.1]
  have H := connectionReturn_cone_direction_bounds hμ ⟨hε.1.le, hε.2⟩ hu hw hv hvu hvw
  have Hd := connectionReturnPhysicalState_differential hμ hu' hw' v
  have Hdec := connectionReturn_exponential_decay hμ hu' hw'
  have Hpos := connectionReturn_wall_pos hμ ⟨hu'.1.le, hu'.2⟩ hw'
  have hphase : |d 0 - 1| ≤ 1 / (4 * p 0) := by
    have heq : d 0 - 1 = fderiv ℝ connectionReturnPhaseError p v := by
      dsimp only [d]
      rw [Hd.1, hv]
      ring
    rw [heq]
    calc
      _ ≤ 200000 * Real.sqrt ε / p 0 := H.1
      _ ≤ (1 / 4) / p 0 := div_le_div_of_nonneg_right (by linarith only [hsε]) hμ0.le
      _ = _ := by ring
  have Hmargin := connection_cone_phase_margin hμ (by linarith only [hL] : 4 ≤ L) hphase
  have hU : Real.sqrt (connectionReturnState p 1) ≤ Real.sqrt (p 1) * Real.exp (-p 0 * L / 4) := by
    have Hb := sqrt_le_sqrt_mul_exp_half hu.1.le Hdec.1
    have heq : (-p 0 * (-Real.log (p 2)) / 2) / 2 = -p 0 * L / 4 := by dsimp only [L]; ring
    rwa [heq] at Hb
  have hV : Real.sqrt (connectionReturnState p 2) ≤ Real.sqrt (p 2) * Real.exp (-L / p 0) := by
    have Hb := sqrt_le_sqrt_mul_exp_half hw.1.le Hdec.2
    have heq : (-2 * (-Real.log (p 2)) / p 0) / 2 = -L / p 0 := by dsimp only [L]; ring
    rwa [heq] at Hb
  let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p
  have hstrong : Real.sqrt (connectionReturnState p 1) * |J v 1| ≤ 1 / 4 := by
    have Hs := connection_strong_cone_size hμ ⟨hε.1.le, by linarith only [hε.2]⟩ hu hw (by linarith only [hL]) hwexp
    have Hb := mul_le_mul hU H.2.1 (abs_nonneg _) (by positivity)
    exact (Hb.trans Hs).trans (by linarith only [hsε])
  have hweak : Real.sqrt (connectionReturnState p 2) * |J v 2| ≤ Real.exp (-L / (2 * p 0)) := by
    have hue : p 1 ≤ ε := hu.2.trans (div_le_self hε.1.le (by linarith only [hμ]))
    have hs : 40000 * Real.sqrt (p 2) ≤ 1 := by
      have Hw := (Real.sqrt_le_sqrt hw.2).trans hsε
      linarith only [Hw]
    have Hs := connection_weak_cone_size hμ ⟨hu.1.le, by linarith only [hue, hε.2]⟩ hw.1 hL hs
    exact (mul_le_mul hV H.2.2 (abs_nonneg _) (by positivity)).trans Hs
  refine ⟨Hmargin.1, hphase, ?_, ?_⟩
  · calc
      |d 1| = Real.sqrt (connectionReturnState p 1) *
          (Real.sqrt (connectionReturnState p 1) * |J v 1|) := by
        dsimp only [d]
        rw [Hd.2.1, abs_mul, abs_of_pos (Hpos.2 hu'.1), ← mul_assoc,
          Real.mul_self_sqrt (Hpos.2 hu'.1).le]
      _ ≤ Real.sqrt (connectionReturnState p 1) * ((1 / 3) * d 0) :=
        mul_le_mul_of_nonneg_left (hstrong.trans Hmargin.2.1) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · calc
      |d 2| = Real.sqrt (connectionReturnState p 2) *
          (Real.sqrt (connectionReturnState p 2) * |J v 2|) := by
        dsimp only [d]
        rw [Hd.2.2, abs_mul, abs_of_pos Hpos.1, ← mul_assoc, Real.mul_self_sqrt Hpos.1.le]
      _ ≤ Real.sqrt (connectionReturnState p 2) *
          ((1 - (1 - Real.exp (-L / (2 * p 0))) / 2) * d 0) :=
        mul_le_mul_of_nonneg_left (hweak.trans Hmargin.2.2) (Real.sqrt_nonneg _)
      _ = _ := by ring
