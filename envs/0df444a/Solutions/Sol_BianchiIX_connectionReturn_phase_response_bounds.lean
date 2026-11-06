-- Prove2me | solution 1 for BianchiIX.connectionReturn_phase_response_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T10:42:54.302853+00:00
-- url     : https://prove2.me/submissions/ca2b256e-4857-40b9-aef8-ff5ceeb2e353

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseEndpointFactor
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_ConnectionClockDifferential
import Definitions.Def_BianchiIX_Dynamics_ConnectionFlowVariation
import Definitions.Def_BianchiIX_Analysis_ConnectionCoefficientMatrix
import Definitions.Def_BianchiIX_Analysis_ConnectionLogCoordinates
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Analysis_ConnectionWeightedVariation
import Definitions.Def_BianchiIX_Analysis_ConnectionFeedbackBounds
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionLogFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturnValues
import Theorems.Thm_BianchiIX_connectionLogField_components
import Theorems.Thm_BianchiIX_connectionLog_prefix_estimates
import Theorems.Thm_BianchiIX_connectionReturn_differential
import Theorems.Thm_BianchiIX_connectionReturn_fixed_clock_bounds
import Theorems.Thm_BianchiIX_connectionReturn_log_amplitude_bounds
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
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

noncomputable section
open BianchiIX

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

private theorem BianchiIX.connection_clock_identities {m u v w : ℝ} (hD : connectionSpeed m u v w ≠ 0) :
    (-m - 1 - coupling u v w) / connectionSpeed m u v w =
      -1 - 2 * (1 + coupling u v w) / connectionSpeed m u v w ∧
    connectionStrongRate m u v w / connectionSpeed m u v w + (m + 1) / 2 =
      (-(v - w) ^ 2 + u ^ 2 - (m + 1) * coupling u v w) / (2 * connectionSpeed m u v w) := by
  constructor <;> dsimp [connectionSpeed, connectionStrongRate] at * <;> field_simp <;> ring

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

private theorem BianchiIX.phaseNorm_ratio_defect {a b : ℝ} (ha : 0 < a) :
    1 - a / phaseNorm a b = b ^ 2 * phaseNormKernel a b := by
  have hn := ne_of_gt (phaseNorm_pos (b := b) ha)
  have hs := ne_of_gt (add_pos (phaseNorm_pos (b := b) ha) ha)
  dsimp [phaseNormKernel]
  field_simp
  nlinarith only [phaseNorm_sq a b]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_interaction {m v w : ℝ} (hm : 1 < m) :
    v ^ 2 * ((m - 1) / phaseNorm (m - 1) w - 1) +
      w ^ 2 * (1 - (m + 1) / phaseNorm (m + 1) v) = (v * w) ^ 2 * matchingPhaseKernel m v w := by
  have hp := phaseNorm_ratio_defect (b := v) (show 0 < m + 1 by linarith only [hm])
  have hn := phaseNorm_ratio_defect (b := w) (show 0 < m - 1 by linarith only [hm])
  have hn' : (m - 1) / phaseNorm (m - 1) w - 1 = -(w ^ 2 * phaseNormKernel (m - 1) w) := by
    linarith only [hn]
  rw [hp, hn']
  unfold matchingPhaseKernel
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_directional {m u v w : ℝ} (hm : 1 < m) :
    matchingPhaseSlope m v w * (-phaseVelocity (-m) u v w) +
      v / phaseNorm (m + 1) v * activeVelocity (-m) u v w +
      w / phaseNorm (m - 1) w * weakVelocity (-m) u v w = matchingPhaseRate m u v w := by
  calc
    _ = v ^ 2 * ((m - 1) / phaseNorm (m - 1) w - 1) +
        w ^ 2 * (1 - (m + 1) / phaseNorm (m + 1) v) -
        u * matchingPhaseSlope m v w * (v - w) - coupling u v w * matchingPhaseWeight m v w := by
      dsimp [matchingPhaseSlope, matchingPhaseWeight, phaseVelocity, activeVelocity, weakVelocity]
      ring
    _ = _ := by rw [matchingPhase_interaction hm]; rfl

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

private theorem BianchiIX.matchingPhase_slope_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 / 4 ≤ matchingPhaseSlope m v w ∧ matchingPhaseSlope m v w ≤ 1 := by
  have hp := phaseNorm_ratio_bounds (by linarith only [hμ, (abs_le.mp hm).1] : 2 ≤ m + 1) hv
  have hn := phaseNorm_ratio_bounds (by linarith only [hμ, (abs_le.mp hm).1] : 2 ≤ m - 1) hw
  dsimp [matchingPhaseSlope]
  constructor <;> linarith only [hp.1, hp.2, hn.1, hn.2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNormKernel_bounds {μ a b : ℝ} (hμ : 0 < μ) (ha : μ / 2 ≤ a) :
    0 ≤ phaseNormKernel a b ∧ phaseNormKernel a b ≤ 2 / μ ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hn := phaseNorm_pos (b := b) ha0
  have hna := phaseNorm_ge (b := b) ha0.le
  have hprod : μ ^ 2 / 2 ≤ phaseNorm a b * (phaseNorm a b + a) := by
    have H := mul_le_mul (ha.trans hna) (show μ ≤ phaseNorm a b + a by linarith only [ha, hna])
      hμ.le hn.le
    nlinarith only [H]
  have hd : 0 < phaseNorm a b * (phaseNorm a b + a) := mul_pos hn (add_pos hn ha0)
  refine ⟨by unfold phaseNormKernel; positivity, ?_⟩
  have H := one_div_le_one_div_of_le (by positivity : 0 < μ ^ 2 / 2) hprod
  exact H.trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_kernel_bound {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2) :
    |matchingPhaseKernel m v w| ≤ 4 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hp := phaseNormKernel_bounds (b := v) hμ0 (by linarith only [hμ, (abs_le.mp hm).1] : μ / 2 ≤ m + 1)
  have hn := phaseNormKernel_bounds (b := w) hμ0 (by linarith only [hμ, (abs_le.mp hm).1] : μ / 2 ≤ m - 1)
  have H := abs_sub (phaseNormKernel (m + 1) v) (phaseNormKernel (m - 1) w)
  rw [abs_of_nonneg hp.1, abs_of_nonneg hn.1] at H
  change |phaseNormKernel (m + 1) v - phaseNormKernel (m - 1) w| ≤ _
  exact (H.trans (add_le_add hp.2 hn.2)).trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_weight_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    0 ≤ matchingPhaseWeight m v w ∧ matchingPhaseWeight m v w ≤ 2 * μ := by
  have hm0 : 0 < m := by linarith only [hμ, (abs_le.mp hm).1]
  have hp := phaseNorm_ge (b := v) (show 0 ≤ m + 1 by linarith only [hm0])
  have hn := phaseNorm_ge (b := w) (show 0 ≤ m - 1 by linarith only [hμ, (abs_le.mp hm).1])
  have hp0 : 0 < phaseNorm (m + 1) v := by linarith only [hp, hm0]
  have hn0 : 0 < phaseNorm (m - 1) w := by linarith only [hn, hμ, (abs_le.mp hm).1]
  have hS := matchingPhase_slope_bounds hμ hm hv hw
  have hS0 : 0 ≤ matchingPhaseSlope m v w := by linarith only [hS.1]
  have hv2 : v ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hv.1 hv.2 2
  have hw2 : w ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hw.1 hw.2 2
  have hvq : v ^ 2 / phaseNorm (m + 1) v ≤ 1 :=
    (div_le_one hp0).mpr (by linarith only [hv2, hp, hm0])
  have hwq : w ^ 2 / phaseNorm (m - 1) w ≤ 1 :=
    (div_le_one hn0).mpr (by linarith only [hw2, hn, hμ, (abs_le.mp hm).1])
  have hprod := mul_le_mul_of_nonneg_left hS.2 hm0.le
  dsimp [matchingPhaseWeight]
  constructor
  · positivity
  · linarith only [hprod, hvq, hwq, hμ, (abs_le.mp hm).2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_rate_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |matchingPhaseRate m u v w| ≤ 5 * μ * u + 4 / μ ^ 2 * (v * w) ^ 2 := by
  have hS := matchingPhase_slope_bounds hμ hm hv hw
  have hS0 : 0 ≤ matchingPhaseSlope m v w := by linarith only [hS.1]
  have hH := matchingPhase_weight_bounds hμ hm hv hw
  have hR := matchingPhase_kernel_bound (v := v) (w := w) hμ hm
  have hC := connection_coupling_bounds hu.1 hv hw
  have hCabs : |coupling u v w| ≤ 2 * u := by
    apply abs_le.mpr
    have H := mul_le_mul_of_nonneg_left (show u ≤ 2 by linarith only [hu.2]) hu.1
    constructor <;> nlinarith only [H, hC.1, hC.2]
  have hdiff : |v - w| ≤ 1 := abs_le.mpr ⟨by linarith only [hv.1, hw.2], by linarith only [hv.2, hw.1]⟩
  have hfirst : |u * matchingPhaseSlope m v w * (v - w)| ≤ u := by
    rw [abs_mul, abs_mul, abs_of_nonneg hu.1, abs_of_nonneg hS0]
    have H := mul_le_mul (mul_le_mul_of_nonneg_left hS.2 hu.1) hdiff (abs_nonneg _)
      (mul_nonneg hu.1 zero_le_one)
    simpa only [mul_one] using H
  have hsecond : |coupling u v w * matchingPhaseWeight m v w| ≤ 4 * μ * u := by
    rw [abs_mul, abs_of_nonneg hH.1]
    have H := mul_le_mul hCabs hH.2 hH.1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu.1)
    nlinarith only [H]
  have hthird : |(v * w) ^ 2 * matchingPhaseKernel m v w| ≤ 4 / μ ^ 2 * (v * w) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left hR (sq_nonneg _)).trans_eq (mul_comm _ _)
  have H := (abs_sub ((v * w) ^ 2 * matchingPhaseKernel m v w - u * matchingPhaseSlope m v w * (v - w))
    (coupling u v w * matchingPhaseWeight m v w)).trans
    (add_le_add (abs_sub _ _) le_rfl)
  change |matchingPhaseRate m u v w| ≤ _ at H
  have huμ := mul_le_mul_of_nonneg_right (show 1 ≤ μ by linarith only [hμ]) hu.1
  nlinarith only [H, hfirst, hsecond, hthird, huμ]

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

private theorem BianchiIX.hasDerivAt_phaseNorm {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (ha0 : 0 < a t) :
    HasDerivAt (fun s => phaseNorm (a s) (b s))
      ((a t * a' + b t * b') / phaseNorm (a t) (b t)) t := by
  have hpos : a t ^ 2 + b t ^ 2 ≠ 0 := by positivity
  convert! ((ha.pow 2).add (hb.pow 2)).sqrt hpos using 1
  dsimp [phaseNorm]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionExitPhaseFactor_sub_one {m v : ℝ} (hm : 1 < m)
    (hf : matchingPhaseSlope m v 1 ≠ 0) :
    connectionExitPhaseFactor m v - 1 = v ^ 2 * phaseNormKernel (m + 1) v / matchingPhaseSlope m v 1 := by
  have H := phaseNorm_ratio_defect (b := v) (show 0 < m + 1 by linarith only [hm])
  rw [connectionExitPhaseFactor, div_sub_one hf]
  have hid : (m - 1) / phaseNorm (m - 1) 1 - matchingPhaseSlope m v 1 =
      1 - (m + 1) / phaseNorm (m + 1) v := by unfold matchingPhaseSlope; ring
  rw [hid, H]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionExitPhaseFactor_bounds {μ m v : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hv : 0 ≤ v ∧ v ≤ 1) :
    0 ≤ connectionExitPhaseFactor m v ∧ connectionExitPhaseFactor m v ≤ 4 / 3 ∧
    |connectionExitPhaseFactor m v - 1| ≤ 4 * v ^ 2 / μ ^ 2 ∧
    0 ≤ v ^ 2 / phaseNorm (m + 1) v ∧ v ^ 2 / phaseNorm (m + 1) v ≤ v ^ 2 / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hm1 : 1 < m := by linarith only [hμ, (abs_le.mp hm).1]
  have hf := (matchingPhase_slope_bounds hμ hm hv ⟨by norm_num, le_rfl⟩).1
  have hf0 : 0 < matchingPhaseSlope m v 1 := by linarith only [hf]
  have hr := phaseNorm_ratio_bounds (by linarith only [hμ, (abs_le.mp hm).1] : 2 ≤ m - 1)
    (show 0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 by norm_num)
  have hr0 : 0 ≤ (m - 1) / phaseNorm (m - 1) 1 := by linarith only [hr.1]
  have hK := phaseNormKernel_bounds (b := v) hμ0
    (show μ / 2 ≤ m + 1 by linarith only [hμ, (abs_le.mp hm).1])
  have hnorm : μ ≤ phaseNorm (m + 1) v :=
    (show μ ≤ m + 1 by linarith only [(abs_le.mp hm).1]).trans (phaseNorm_ge (by linarith only [hm1]))
  refine ⟨div_nonneg hr0 hf0.le, ?_, ?_, div_nonneg (sq_nonneg v) (hμ0.le.trans hnorm),
    div_le_div_of_nonneg_left (sq_nonneg v) hμ0 hnorm⟩
  · exact (div_le_iff₀ hf0).mpr (by linarith only [hr.2, hf])
  · rw [connectionExitPhaseFactor_sub_one hm1 (ne_of_gt hf0),
      abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg v) hK.1) hf0.le)]
    have H := div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg v) hK.1) (by norm_num : (0 : ℝ) < 3 / 4) hf
    calc
      v ^ 2 * phaseNormKernel (m + 1) v / matchingPhaseSlope m v 1 ≤
          v ^ 2 * phaseNormKernel (m + 1) v / (3 / 4) := H
      _ ≤ v ^ 2 * (2 / μ ^ 2) / (3 / 4) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK.2 (sq_nonneg v)) (by norm_num)
      _ ≤ 4 * v ^ 2 / μ ^ 2 := by
        have hq : 0 ≤ v ^ 2 / μ ^ 2 := div_nonneg (sq_nonneg v) (sq_nonneg μ)
        simp only [div_eq_mul_inv] at hq ⊢
        nlinarith only [hq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_entry_slope_defect {μ w : ℝ} (hμ : 4 ≤ μ) :
    |matchingPhaseSlope μ 1 w - (μ + 1) / phaseNorm (μ + 1) 1| ≤ 2 * w ^ 2 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hK := phaseNormKernel_bounds (b := w) hμ0 (show μ / 2 ≤ μ - 1 by linarith only [hμ])
  have H := phaseNorm_ratio_defect (b := w) (show 0 < μ - 1 by linarith only [hμ])
  have hid : matchingPhaseSlope μ 1 w - (μ + 1) / phaseNorm (μ + 1) 1 =
      -(w ^ 2 * phaseNormKernel (μ - 1) w) := by unfold matchingPhaseSlope; linarith only [H]
  rw [hid, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg w) hK.1)]
  exact (mul_le_mul_of_nonneg_left hK.2 (sq_nonneg w)).trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.affine_mul_exp_neg_le_one (x : ℝ) : (1 + x) * Real.exp (-x) ≤ 1 := by
  have H := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at H
  simpa only [add_comm] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_endpoint_envelope_bounds {μ u w U V : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u) (hw : 0 < w ∧ w ≤ 1 / 10000) (hV : 0 ≤ V)
    (hU : U ≤ u * Real.exp (-μ * (-Real.log w) / 2))
    (hdecay : V ≤ w * Real.exp (-2 * (-Real.log w) / μ)) :
    U / w ≤ 8 * u / μ ∧ V ^ 2 ≤ w ^ 2 ∧ (1 - Real.log w) * V ^ 2 ≤ μ * w ^ 2 := by
  let L := -Real.log w
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hL : 1 / 2 ≤ L := by
    have H := Real.log_le_sub_one_of_pos hw.1
    dsimp [L]
    linarith only [H, hw.2]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hwexp : w = Real.exp (-L) := by simp [L, Real.exp_log hw.1]
  have hstrong : Real.exp (-μ * L / 4) ≤ 8 / μ := by
    apply (le_div_iff₀ hμ0).mpr
    have H := affine_mul_exp_neg_le_one (μ * L / 4)
    rw [show -(μ * L / 4) = -μ * L / 4 by ring] at H
    have Hl := mul_le_mul_of_nonneg_right hL (show 0 ≤ μ * Real.exp (-μ * L / 4) by positivity)
    nlinarith only [H, Hl, Real.exp_pos (-μ * L / 4)]
  have hv2 : V ^ 2 ≤ w ^ 2 * Real.exp (-4 * L / μ) := by
    have H := pow_le_pow_left₀ hV hdecay 2
    rw [mul_pow, ← Real.exp_nat_mul] at H
    convert! H using 1
    congr 2
    ring
  have hexp : Real.exp (-4 * L / μ) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by linarith only [hL0]) hμ0.le)
  refine ⟨?_, (hv2.trans (mul_le_mul_of_nonneg_left hexp (sq_nonneg w))).trans_eq (mul_one _), ?_⟩
  · calc
      U / w ≤ (u * Real.exp (-μ * L / 2)) / w := div_le_div_of_nonneg_right hU hw.1.le
      _ = u * Real.exp (-μ * L / 2 - (-L)) := by rw [hwexp, Real.exp_sub]; ring
      _ ≤ u * Real.exp (-μ * L / 4) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith only [hμ, hL0])) hu
      _ ≤ u * (8 / μ) := mul_le_mul_of_nonneg_left hstrong hu
      _ = 8 * u / μ := by ring
  · have H := affine_mul_exp_neg_le_one (4 * L / μ)
    rw [show -(4 * L / μ) = -4 * L / μ by ring] at H
    have hweight : 1 + L ≤ μ * (1 + 4 * L / μ) := by
      have hid : μ * (1 + 4 * L / μ) = μ + 4 * L := by field_simp
      rw [hid]
      linarith only [hμ, hL0]
    have Hb : (1 + L) * Real.exp (-4 * L / μ) ≤ μ := by
      have H1 := mul_le_mul_of_nonneg_right hweight (Real.exp_pos (-4 * L / μ)).le
      have H2 := mul_le_mul_of_nonneg_left H hμ0.le
      nlinarith only [H1, H2]
    change (1 + L) * V ^ 2 ≤ μ * w ^ 2
    calc
      (1 + L) * V ^ 2 ≤ (1 + L) * (w ^ 2 * Real.exp (-4 * L / μ)) :=
        mul_le_mul_of_nonneg_left hv2 (by positivity)
      _ = w ^ 2 * ((1 + L) * Real.exp (-4 * L / μ)) := by ring
      _ ≤ w ^ 2 * μ := mul_le_mul_of_nonneg_left Hb (sq_nonneg w)
      _ = μ * w ^ 2 := mul_comm _ _

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

private theorem BianchiIX.connectionLogField_amplitude {y : ProjectiveState} (hD : connectionClockRate y ≠ 0) :
    connectionLogField y 1 = connectionStrongClockRate (-y 0) (y 1) (y 2) (y 3) * y 1 ∧
    connectionLogField y 2 = connectionWeakClockRate (-y 0) (y 1) (y 2) (y 3) * y 2 := by
  have H := connectionLogField_components hD
  have hb := (connection_clock_identities hD).1
  simp only [neg_neg] at hb
  refine ⟨H.2.1, ?_⟩
  rw [H.2.2.1]
  dsimp only [connectionClockRate, connectionWeakClockRate]
  rw [hb]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionLog_amplitudes {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hD : connectionClockRate (Y t) ≠ 0)
    (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) :
    HasDerivAt (fun s => Real.log (Y s 1)) (connectionStrongClockRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t ∧
    HasDerivAt (fun s => Real.log (Y s 2)) (connectionWeakClockRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t := by
  have H := connectionLogField_amplitude hD
  constructor
  · apply ((hasDerivAt_pi.mp hY 1).log hu).congr_deriv
    rw [H.1, mul_div_cancel_right₀ _ hu]
  · apply ((hasDerivAt_pi.mp hY 2).log hv).congr_deriv
    rw [H.2, mul_div_cancel_right₀ _ hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_matchingPhase_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t) (hm : 1 < -Y t 0) :
    HasDerivAt (fun s => matchingPhase (-Y s 0) (Y s 2) (Y s 3))
      (a * matchingPhaseRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t := by
  have H := hasDerivAt_matchingPhase (hasDerivAt_pi.mp hY 0).neg
    (hasDerivAt_pi.mp hY 2) (hasDerivAt_pi.mp hY 3) hm
  simp only [Pi.neg_apply] at H
  have hrate := matchingPhase_directional (u := Y t 1) (v := Y t 2) (w := Y t 3) hm
  simp only [neg_neg] at hrate
  convert! H using 1
  rw [← hrate]
  change a * _ = matchingPhaseSlope _ _ _ * (-(a * phaseVelocity _ _ _ _)) +
    _ * (a * activeVelocity _ _ _ _) + _ * (a * weakVelocity _ _ _ _)
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_matchingPhase_connectionLog {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hm : 1 < -Y t 0) :
    HasDerivAt (fun s => matchingPhase (-Y s 0) (Y s 2) (Y s 3))
      (matchingPhaseRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3) / connectionClockRate (Y t)) t := by
  convert! hasDerivAt_matchingPhase_scaled hY hm using 1
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionLog_system {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hm : 1 < -Y t 0)
    (hD : connectionClockRate (Y t) ≠ 0) (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) :
    HasDerivAt (fun s => (![matchingPhase (-Y s 0) (Y s 2) (Y s 3),
      Real.log (Y s 1), Real.log (Y s 2)] : Fin 3 → ℝ))
      (connectionLogRates (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t := by
  have hG := hasDerivAt_matchingPhase_connectionLog hY hm
  have hab := hasDerivAt_connectionLog_amplitudes hY hD hu hv
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hG
  · exact hab.1
  · exact hab.2

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

private theorem BianchiIX.hasDerivAt_connectionLogCoordinates_flow {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hm : 1 < -Y t 0)
    (hD : connectionClockRate (Y t) ≠ 0) (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) (hw : Y t 3 ≠ 0) :
    HasDerivAt (fun s => connectionLogCoordinates (Y s)) (connectionLogCoordinateRates (Y t)) t := by
  have H := hasDerivAt_connectionLog_system hY hm hD hu hv
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp H 0
  · exact hasDerivAt_pi.mp H 1
  · exact hasDerivAt_pi.mp H 2
  · apply ((hasDerivAt_pi.mp hY 3).log hw).congr_deriv
    rw [(connectionLogField_components hD).2.2.2, div_self hw]
    rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionLogCoordinates_fderiv_field {y : ProjectiveState}
    (hm : 1 < -y 0) (hD : connectionClockRate y ≠ 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) :
    fderiv ℝ connectionLogCoordinates y (connectionLogField y) = connectionLogCoordinateRates y := by
  have hline : HasDerivAt (fun s : ℝ => y + s • connectionLogField y) (connectionLogField y) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (connectionLogField y)).const_add y
  have hY : HasDerivAt (fun s : ℝ => y + s • connectionLogField y)
      (connectionLogField (y + (0 : ℝ) • connectionLogField y)) 0 := by simpa using hline
  have H1 := hasDerivAt_connectionLogCoordinates hY (by simpa using hm)
    (by simpa using hu) (by simpa using hv) (by simpa using hw)
  have H2 := hasDerivAt_connectionLogCoordinates_flow hY (by simpa using hm) (by simpa using hD)
    (by simpa using hu) (by simpa using hv) (by simpa using hw)
  rw [connectionLogCoordinates_fderiv hm hu hv hw]
  simpa only [zero_smul, add_zero] using H1.unique H2

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

private theorem BianchiIX.connectionExitPhase_response_bound {μ m v : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hv : 0 ≤ v ∧ v ≤ 1) (Z Y : ℝ) :
    |connectionExitPhaseFactor m v * (Z - (v ^ 2 / phaseNorm (m + 1) v) * Y)| ≤
      (4 / 3) * (|Z| + (v ^ 2 / μ) * |Y|) := by
  obtain ⟨hA0, hA, _, hQ0, hQ⟩ := connectionExitPhaseFactor_bounds hμ hm hv
  rw [abs_mul, abs_of_nonneg hA0]
  apply (mul_le_mul_of_nonneg_left (abs_sub _ _) hA0).trans
  rw [abs_mul, abs_of_nonneg hQ0]
  exact mul_le_mul hA (add_le_add le_rfl (mul_le_mul_of_nonneg_right hQ (abs_nonneg Y)))
    (by positivity) (by norm_num)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionExitPhase_radial_error_bound {μ m v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hv : 0 ≤ v ∧ v ≤ 1) (Z Y : ℝ) :
    |connectionExitPhaseFactor m v * (Z - (v ^ 2 / phaseNorm (m + 1) v) * Y) -
      (μ + 1) / phaseNorm (μ + 1) 1| ≤
    |Z - matchingPhaseSlope μ 1 w| + (4 * v ^ 2 / μ ^ 2) * |Z| +
      (4 / 3) * ((v ^ 2 / μ) * |Y|) + 2 * w ^ 2 / μ ^ 2 := by
  obtain ⟨hA0, hA, hAd, hQ0, hQ⟩ := connectionExitPhaseFactor_bounds hμ hm hv
  let A := connectionExitPhaseFactor m v
  let Q := v ^ 2 / phaseNorm (m + 1) v
  let F := matchingPhaseSlope μ 1 w
  let R := (μ + 1) / phaseNorm (μ + 1) 1
  have hid : A * (Z - Q * Y) - R = (Z - F) + (A - 1) * Z - A * (Q * Y) + (F - R) := by ring
  change |A * (Z - Q * Y) - R| ≤ _
  rw [hid]
  have H := (abs_add_le ((Z - F) + (A - 1) * Z - A * (Q * Y)) (F - R)).trans
    (add_le_add ((abs_sub ((Z - F) + (A - 1) * Z) (A * (Q * Y))).trans
      (add_le_add (abs_add_le (Z - F) ((A - 1) * Z)) le_rfl)) le_rfl)
  have Hb : |A * (Q * Y)| ≤ (4 / 3) * ((v ^ 2 / μ) * |Y|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg hQ0]
    exact mul_le_mul hA (mul_le_mul_of_nonneg_right hQ (abs_nonneg Y)) (by positivity) (by norm_num)
  have Ha : |(A - 1) * Z| ≤ (4 * v ^ 2 / μ ^ 2) * |Z| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hAd (abs_nonneg Z)
  have He : |F - R| ≤ 2 * w ^ 2 / μ ^ 2 := matchingPhase_entry_slope_defect hμ
  exact H.trans (add_le_add (add_le_add (add_le_add le_rfl Ha) Hb) He)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseFeedbackBudget_scale {μ u w : ℝ} (hμ : 4 ≤ μ) (hu : 0 ≤ u) :
    (16 / 15) * connectionPhaseFeedbackBudget μ u w ≤ 35000 * (u + w ^ 2) / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hU : u / μ ^ 3 ≤ (u / μ ^ 2) / 4 := by
    calc
      u / μ ^ 3 = (u / μ ^ 2) / μ := by ring
      _ ≤ (u / μ ^ 2) / 4 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hμ
  have hW : w ^ 2 / μ ^ 3 ≤ (w ^ 2 / μ ^ 2) / 4 := by
    calc
      w ^ 2 / μ ^ 3 = (w ^ 2 / μ ^ 2) / μ := by ring
      _ ≤ (w ^ 2 / μ ^ 2) / 4 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hμ
  have hU0 : 0 ≤ u / μ ^ 2 := by positivity
  have hW0 : 0 ≤ w ^ 2 / μ ^ 2 := by positivity
  have hid : connectionPhaseFeedbackBudget μ u w =
      128 * (u / μ ^ 3) + 32768 * (u / μ ^ 2) + 528 * (w ^ 2 / μ ^ 3) := by
    unfold connectionPhaseFeedbackBudget
    ring
  rw [hid]
  simp only [div_eq_mul_inv] at hU hW hU0 hW0 ⊢
  nlinarith only [hU, hW, hU0, hW0]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_endpoint_weighted_log_bound {μ v w L C Y : ℝ} (hμ : 0 < μ) (hC : 0 ≤ C)
    (hweight : (1 + L) * v ^ 2 ≤ μ * w ^ 2) (hY : |Y| ≤ C * (1 + L) / μ ^ 2) :
    (v ^ 2 / μ) * |Y| ≤ C * w ^ 2 / μ ^ 2 := by
  calc
    (v ^ 2 / μ) * |Y| ≤ (v ^ 2 / μ) * (C * (1 + L) / μ ^ 2) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    _ = C * ((1 + L) * v ^ 2) / μ ^ 3 := by ring
    _ ≤ C * (μ * w ^ 2) / μ ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hweight hC) (by positivity)
    _ = C * w ^ 2 / μ ^ 2 := by field_simp

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

private theorem BianchiIX.contDiffAt_connectionInitialState (n : WithTop ℕ∞) {p : ConnectionParameters}
    (hD : projectiveStateDenom (connectionEntry (p 0) (p 1) (p 2)) ≠ 0) :
    ContDiffAt ℝ n connectionInitialState p := by
  apply (contDiffAt_fromProjectiveState n hD).comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [connectionEntry] <;> fun_prop

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

private theorem BianchiIX.connectionLogTangent_arrival_correction {y v : ProjectiveState} (ζ : ℝ)
    (hm : 1 < -y 0) (hD : connectionClockRate y ≠ 0)
    (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) :
    connectionLogTangent y (connectionClockProjection y v 0) =
      connectionLogTangent y (connectionClockProjection y v ζ) - ζ • connectionLogCoordinateRates y := by
  have hid : connectionClockProjection y v 0 = connectionClockProjection y v ζ - ζ • connectionLogField y := by
    unfold connectionClockProjection
    module
  rw [← connectionLogCoordinates_fderiv hm hu hv hw, hid, map_sub, map_smul,
    connectionLogCoordinates_fderiv_field hm hD hu hv hw, connectionLogCoordinates_fderiv hm hu hv hw]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_growing_projection_eq_clock {y v : ProjectiveState}
    (hD : connectionClockRate y ≠ 0) (hw : y 3 ≠ 0) :
    v - (v 3 / projectiveField y 3) • projectiveField y = connectionClockProjection y v 0 := by
  have hfield : projectiveField y 3 = connectionClockRate y * y 3 := rfl
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, connectionClockProjection, sub_zero,
    connectionLogField, hfield]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionInitialState_fderiv {p : ConnectionParameters}
    (hD : projectiveStateDenom (connectionEntry (p 0) (p 1) (p 2)) ≠ 0) (v : ConnectionParameters) :
    fderiv ℝ connectionInitialState p v =
      fderiv ℝ fromProjectiveState (connectionEntry (p 0) (p 1) (p 2)) ![-v 0, v 1, 0, v 2] := by
  have hline : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hentry : HasDerivAt (fun s : ℝ => connectionEntry ((p + s • v) 0) ((p + s • v) 1) ((p + s • v) 2))
      ![-v 0, v 1, 0, v 2] 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (hasDerivAt_pi.mp hline 0).neg
    · exact hasDerivAt_pi.mp hline 1
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_pi.mp hline 2
  have hfrom := ((contDiffAt_fromProjectiveState 1 hD).differentiableAt (by norm_num)).hasFDerivAt
  have hfrom' : HasFDerivAt fromProjectiveState
      (fderiv ℝ fromProjectiveState (connectionEntry (p 0) (p 1) (p 2)))
      (connectionEntry ((p + (0 : ℝ) • v) 0) ((p + (0 : ℝ) • v) 1) ((p + (0 : ℝ) • v) 2)) := by simpa using hfrom
  have H := hfrom'.comp_hasDerivAt 0 hentry
  have hinit := ((contDiffAt_connectionInitialState 1 hD).differentiableAt (by norm_num)).hasFDerivAt
  have hinit' : HasFDerivAt connectionInitialState (fderiv ℝ connectionInitialState p) (p + (0 : ℝ) • v) := by simpa using hinit
  exact (hinit'.comp_hasDerivAt 0 hline).unique H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionReturn_log_differential {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000)
    (v : ConnectionParameters) :
    fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p v =
      connectionLogFlowVariation (connectionEntry (p 0) (p 1) (p 2)) 0 (connectionReturnTime p) ![-v 0, v 1, 0, v 2] -
        (v 2 / p 2) • connectionLogCoordinateRates (connectionReturnState p) := by
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0 := ⟨hu.1.le, hu.2⟩
  have hregular := connectionReturn_regular hμ hu' hw
  have hcontrol := connectionReturn_control hμ hu' hw
  have hregion := (hcontrol.2 (connectionReturnTime p) ⟨hcontrol.1.le, le_rfl⟩).2
  change connectionRegion (p 0) (connectionReturnState p) at hregion
  have hm : 1 < -connectionReturnState p 0 := by linarith only [hμ, (abs_le.mp hregion.1).1]
  have hD : connectionClockRate (connectionReturnState p) ≠ 0 := by
    have H := (connection_speed_bounds hμ hregion.1 hregion.2.1 hregion.2.2.1 hregion.2.2.2).1
    change p 0 / 2 ≤ connectionClockRate (connectionReturnState p) at H
    linarith only [H, hμ]
  have hpos := connectionReturn_wall_pos hμ hu' hw
  have hU := ne_of_gt (hpos.2 hu.1)
  have hV := ne_of_gt hpos.1
  have hW : connectionReturnState p 3 ≠ 0 := by rw [(connectionReturn_growing_component hμ hu' hw).1]; norm_num
  rw [fderiv_comp p ((contDiffAt_connectionLogCoordinates 1 hm hU hV hW).differentiableAt (by norm_num))
    (hregular.2.2.1.differentiableAt (by norm_num)), ContinuousLinearMap.comp_apply,
    connectionLogCoordinates_fderiv hm hU hV hW]
  have hd := (connectionReturn_differential hμ hu' hw v).2
  rw [connectionInitialState_fderiv (ne_of_gt (connection_entry_denom_pos hμ hu' hw))] at hd
  change fderiv ℝ connectionReturnState p v =
    projectiveFlowDifferential (connectionEntry (p 0) (p 1) (p 2)) 0 (connectionReturnTime p) ![-v 0, v 1, 0, v 2] -
      ((projectiveFlowDifferential (connectionEntry (p 0) (p 1) (p 2)) 0 (connectionReturnTime p) ![-v 0, v 1, 0, v 2]) 3 /
        projectiveField (connectionReturnState p) 3) • projectiveField (connectionReturnState p) at hd
  rw [hd, connection_growing_projection_eq_clock hD hW,
    connectionLogTangent_arrival_correction (v 2 / p 2) hm hD hU hV hW]
  rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionExitPhase_tangent {y v : ProjectiveState} (hw : y 3 = 1)
    (hf : matchingPhaseSlope (-y 0) (y 2) 1 ≠ 0) (hvw : v 3 = 0) :
    ((-y 0 - 1) / phaseNorm (-y 0 - 1) 1) * (-v 0) =
      connectionExitPhaseFactor (-y 0) (y 2) * (connectionLogTangent y v 0 -
        ((y 2) ^ 2 / phaseNorm (-y 0 + 1) (y 2)) * connectionLogTangent y v 2) := by
  simp [connectionExitPhaseFactor, connectionLogTangent, hw, hvw]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionReturnPhaseError_differential {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000)
    (v : ConnectionParameters) :
    let y := connectionReturnState p
    let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p v
    fderiv ℝ connectionReturnPhaseError p v =
      connectionExitPhaseFactor (-y 0) (y 2) *
        (J 0 - ((y 2) ^ 2 / phaseNorm (-y 0 + 1) (y 2)) * J 2) -
      ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 := by
  intro y J
  let ξ := fderiv ℝ connectionReturnState p v
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0 := ⟨hu.1.le, hu.2⟩
  have hc := connectionReturn_control hμ hu' hw
  have hr := (hc.2 (connectionReturnTime p) ⟨hc.1.le, le_rfl⟩).2
  change connectionRegion (p 0) y at hr
  have hm : 1 < -y 0 := by linarith only [hμ, (abs_le.mp hr.1).1]
  have hpos := connectionReturn_wall_pos hμ hu' hw
  have hU : y 1 ≠ 0 := ne_of_gt (hpos.2 hu.1)
  have hV : y 2 ≠ 0 := ne_of_gt hpos.1
  have hW : y 3 = 1 := (connectionReturn_growing_component hμ hu' hw).1
  have hξW : ξ 3 = 0 := (connectionReturn_growing_component hμ hu' hw).2 v
  have hf : matchingPhaseSlope (-y 0) (y 2) 1 ≠ 0 := by
    have H := (matchingPhase_slope_bounds hμ hr.1 hr.2.2.1 ⟨by norm_num, le_rfl⟩).1
    linarith only [H]
  have hstate := ((connectionReturn_regular hμ hu' hw).2.2.1.differentiableAt (by norm_num)).hasFDerivAt
  have hJ : J = connectionLogTangent y ξ := by
    dsimp [J]
    rw [fderiv_comp p ((contDiffAt_connectionLogCoordinates 1 hm hU hV (by rw [hW]; norm_num)).differentiableAt (by norm_num))
      hstate.differentiableAt, ContinuousLinearMap.comp_apply, connectionLogCoordinates_fderiv hm hU hV (by rw [hW]; norm_num)]
  have hline : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hstate' : HasFDerivAt connectionReturnState (fderiv ℝ connectionReturnState p) (p + (0 : ℝ) • v) := by
    simpa using hstate
  have hpath := hstate'.comp_hasDerivAt 0 hline
  have hout := hasDerivAt_phaseNorm ((hasDerivAt_pi.mp hpath 0).neg.sub_const 1) (hasDerivAt_const 0 (1 : ℝ))
    (by simpa [Function.comp_def, y] using (show 0 < -y 0 - 1 by linarith only [hm]))
  have hin := hasDerivAt_phaseNorm ((hasDerivAt_pi.mp hline 0).add_const 1) (hasDerivAt_const 0 (1 : ℝ))
    (by simpa using (show 0 < p 0 + 1 by linarith only [hμ]))
  have hdelta : HasFDerivAt connectionReturnPhaseError (fderiv ℝ connectionReturnPhaseError p) (p + (0 : ℝ) • v) := by
    simpa using ((contDiffAt_connectionReturnPhaseError hμ hu' hw).differentiableAt (by norm_num)).hasFDerivAt
  have hraw : fderiv ℝ connectionReturnPhaseError p v =
      ((-y 0 - 1) / phaseNorm (-y 0 - 1) 1) * (-ξ 0) -
      ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 := by
    have hdline : HasDerivAt (fun s : ℝ => connectionReturnPhaseError (p + s • v))
        (fderiv ℝ connectionReturnPhaseError p v) 0 :=
      HasFDerivAt.comp_hasDerivAt (l := connectionReturnPhaseError)
        (l' := fderiv ℝ connectionReturnPhaseError p) (f := fun s : ℝ => p + s • v) 0 hdelta hline
    have hcalc : HasDerivAt (fun s : ℝ => connectionReturnPhaseError (p + s • v))
        (((-y 0 - 1) / phaseNorm (-y 0 - 1) 1) * (-ξ 0) -
          ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0) 0 := by
      simpa [connectionReturnPhaseError, Function.comp_def, y, ξ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using (hout.sub hin).add_const 2
    exact hdline.unique hcalc
  rw [hraw, hJ, connectionExitPhase_tangent hW hf hξW]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.connectionReturn_endpoint_scales {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    connectionReturnState p 1 / p 2 ≤ 8 * p 1 / p 0 ∧
    (connectionReturnState p 2) ^ 2 ≤ (p 2) ^ 2 ∧
    (1 - Real.log (p 2)) * (connectionReturnState p 2) ^ 2 ≤ p 0 * (p 2) ^ 2 := by
  let y := connectionEntry (p 0) (p 1) (p 2)
  let L := -Real.log (p 2)
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
  have hUdecay : connectionReturnState p 1 ≤ p 1 * Real.exp (-p 0 * L / 2) := by
    have Hs := HP.2.1
    change Y L 1 ≤ Y 0 1 * Real.exp (-p 0 * (L - 0) / 2) at Hs
    simpa [hinit, hend, y, connectionEntry] using Hs
  have hVdecay : connectionReturnState p 2 ≤ p 2 * Real.exp (-2 * L / p 0) := by
    have Hs := HP.2.2.2.1
    change Y L 2 * Y L 3 ≤ Y 0 2 * Y 0 3 * Real.exp (-2 * (L - 0) / p 0) at Hs
    rw [hend, hinit, (connectionReturn_growing_component hμ ⟨hu.1.le, hu.2⟩ hw).1] at Hs
    simpa [y, connectionEntry] using Hs
  exact connection_endpoint_envelope_bounds hμ hu.1.le hw
    (connectionReturn_wall_pos hμ ⟨hu.1.le, hu.2⟩ hw).1.le hUdecay hVdecay

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.connectionReturn_phase_clock_correction {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    |connectionLogCoordinateRates (connectionReturnState p) 0| / p 2 ≤ 100 * (p 1 + p 2) / p 0 := by
  let μ := p 0
  let u := p 1
  let w := p 2
  let y := connectionReturnState p
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hw0 : 0 < w := hw.1
  have hscales := connectionReturn_endpoint_scales hμ hu hw
  have hc := connectionReturn_control hμ ⟨hu.1.le, hu.2⟩ hw
  have hr := (hc.2 (connectionReturnTime p) ⟨hc.1.le, le_rfl⟩).2
  change connectionRegion μ y at hr
  have hW : y 3 = 1 := (connectionReturn_growing_component hμ ⟨hu.1.le, hu.2⟩ hw).1
  have hD := (connection_speed_bounds hμ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2).1
  have hD0 : 0 < connectionSpeed (-y 0) (y 1) (y 2) (y 3) := by linarith only [hD, hμ]
  have hrate : |connectionLogCoordinateRates y 0| ≤ 10 * y 1 + 8 * (y 2) ^ 2 / μ ^ 3 := by
    change |matchingPhaseRate (-y 0) (y 1) (y 2) (y 3) / connectionSpeed (-y 0) (y 1) (y 2) (y 3)| ≤ _
    rw [abs_div, abs_of_pos hD0]
    have H := matchingPhase_rate_bound hμ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
    have H' : |matchingPhaseRate (-y 0) (y 1) (y 2) (y 3)| ≤ 5 * μ * y 1 + 4 / μ ^ 2 * (y 2) ^ 2 := by
      simpa only [hW, mul_one] using H
    calc
      _ ≤ (5 * μ * y 1 + 4 / μ ^ 2 * (y 2) ^ 2) / connectionSpeed (-y 0) (y 1) (y 2) (y 3) :=
        div_le_div_of_nonneg_right H' hD0.le
      _ ≤ (5 * μ * y 1 + 4 / μ ^ 2 * (y 2) ^ 2) / (μ / 2) :=
        div_le_div_of_nonneg_left (by have H0 := hr.2.1.1; positivity) (by positivity) hD
      _ = 10 * y 1 + 8 * (y 2) ^ 2 / μ ^ 3 := by field_simp; ring
  have hweak : (y 2) ^ 2 / (μ ^ 3 * w) ≤ w / μ := by
    have H : (y 2) ^ 2 / w ≤ w := (div_le_iff₀ hw0).mpr (by nlinarith only [hscales.2.1])
    calc
      (y 2) ^ 2 / (μ ^ 3 * w) = ((y 2) ^ 2 / w) / μ ^ 3 := by ring
      _ ≤ w / μ ^ 3 := div_le_div_of_nonneg_right H (by positivity)
      _ ≤ w / μ := div_le_div_of_nonneg_left hw0.le hμ0 (by nlinarith only [hμ, sq_nonneg (μ - 1)])
  change |connectionLogCoordinateRates y 0| / w ≤ 100 * (u + w) / μ
  calc
    _ ≤ (10 * y 1 + 8 * (y 2) ^ 2 / μ ^ 3) / w := div_le_div_of_nonneg_right hrate hw0.le
    _ = 10 * (y 1 / w) + 8 * ((y 2) ^ 2 / (μ ^ 3 * w)) := by ring
    _ ≤ 10 * (8 * u / μ) + 8 * (w / μ) := add_le_add
      (mul_le_mul_of_nonneg_left hscales.1 (by norm_num)) (mul_le_mul_of_nonneg_left hweak (by norm_num))
    _ = (80 * u + 8 * w) / μ := by ring
    _ ≤ 100 * (u + w) / μ := by
      apply div_le_div_of_nonneg_right _ hμ0.le
      have hu0 : 0 < u := hu.1
      nlinarith only [hu0, hw0]

end
end

/-- The three ordinary phase-error derivatives of the exact positive-wall first return. -/
theorem solution {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    |fderiv ℝ connectionReturnPhaseError p ![1, 0, 0]| ≤ 50000 * (p 1 + (p 2) ^ 2) / (p 0) ^ 2 ∧
    |fderiv ℝ connectionReturnPhaseError p ![0, 1, 0]| ≤ 50000 / p 0 ∧
    |fderiv ℝ connectionReturnPhaseError p ![0, 0, 1]| ≤ 50000 * (p 1 + p 2) / p 0 := by
  let μ := p 0
  let u := p 1
  let w := p 2
  let L := -Real.log w
  let y := connectionReturnState p
  let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p
  let D := connectionLogFlowVariation (connectionEntry μ u w) 0 (connectionReturnTime p)
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hu0 : 0 < u := hu.1
  have hw0 : 0 < w := hw.1
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hw0.le (by linarith only [hw.2]))
  have hrad : J ![1, 0, 0] = D ![-1, 0, 0, 0] := by
    simpa [J, D, μ, u, w] using connectionReturn_log_differential hμ hu hw ![1, 0, 0]
  have hstrong : J ![0, 1, 0] = D ![0, 1, 0, 0] := by
    simpa [J, D, μ, u, w] using connectionReturn_log_differential hμ hu hw ![0, 1, 0]
  have hgrowing : J ![0, 0, 1] = D ![0, 0, 0, 1] - (1 / w) • connectionLogCoordinateRates y := by
    simpa [J, D, y, μ, u, w] using connectionReturn_log_differential hμ hu hw ![0, 0, 1]
  have H := connectionReturn_fixed_clock_bounds hμ hu hw
  have HA := connectionReturn_log_amplitude_bounds hμ hu hw
  have HS := connectionReturn_endpoint_scales hμ hu hw
  have hc := connectionReturn_control hμ ⟨hu.1.le, hu.2⟩ hw
  have hr := (hc.2 (connectionReturnTime p) ⟨hc.1.le, le_rfl⟩).2
  change connectionRegion μ y at hr
  have hv2 : (y 2) ^ 2 ≤ w ^ 2 := HS.2.1
  have hweight : (1 + L) * (y 2) ^ 2 ≤ μ * w ^ 2 := HS.2.2
  have hzμ : |J ![1, 0, 0] 0| ≤ 16 / 15 := by rw [hrad]; exact H.1.1
  have hdμ : |J ![1, 0, 0] 0 - matchingPhaseSlope μ 1 w| ≤ 35000 * (u + w ^ 2) / μ ^ 2 := by
    rw [hrad]
    have H0 : |D ![-1, 0, 0, 0] 0 - matchingPhaseSlope μ 1 w| ≤
        (16 / 15) * connectionPhaseFeedbackBudget μ u w := by
      simpa [D, μ, u, w, connectionLogTangent, connectionEntry] using H.1.2.1
    exact H0.trans (connectionPhaseFeedbackBudget_scale hμ hu0.le)
  have hzU : |J ![0, 1, 0] 0| ≤ 70 / μ := by rw [hstrong]; exact H.2.1.1
  have hzW : |J ![0, 0, 1] 0| ≤ 8100 * (u + w) / μ := by
    rw [hgrowing]
    have Htri := abs_sub (D ![0, 0, 0, 1] 0) ((1 / w) * connectionLogCoordinateRates y 0)
    have Hc : |(1 / w) * connectionLogCoordinateRates y 0| ≤ 100 * (u + w) / μ := by
      simpa [abs_mul, abs_of_pos hw0, div_eq_mul_inv, mul_comm] using connectionReturn_phase_clock_correction hμ hu hw
    exact (Htri.trans (add_le_add H.2.2.1 Hc)).trans_eq (by ring)
  have hyμ : ((y 2) ^ 2 / μ) * |J ![1, 0, 0] 2| ≤ 137 * w ^ 2 / μ ^ 2 := by
    apply connection_endpoint_weighted_log_bound hμ0 (by norm_num) hweight
    exact HA.2.1.trans (div_le_div_of_nonneg_right (by nlinarith only [hL]) (sq_nonneg μ))
  have hyU : ((y 2) ^ 2 / μ) * |J ![0, 1, 0] 2| ≤ 9000 * w ^ 2 / μ ^ 2 :=
    connection_endpoint_weighted_log_bound hμ0 (by norm_num) hweight HA.2.2.2.1
  have hyW : ((y 2) ^ 2 / μ) * |J ![0, 0, 1] 2| ≤ 9 * w / μ := by
    have h32 : 32 / μ ≤ 8 := (div_le_iff₀ hμ0).mpr (by linarith only [hμ])
    have HY : |J ![0, 0, 1] 2| ≤ 9 / w := HA.2.2.2.2.2.trans
      (div_le_div_of_nonneg_right (by linarith only [h32]) hw0.le)
    calc
      _ ≤ ((y 2) ^ 2 / μ) * (9 / w) := mul_le_mul_of_nonneg_left HY (by positivity)
      _ ≤ (w ^ 2 / μ) * (9 / w) := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hv2 hμ0.le) (by positivity)
      _ = 9 * w / μ := by field_simp
  have hformula (v : ConnectionParameters) := connectionReturnPhaseError_differential hμ hu hw v
  have hsmall : w ^ 2 / μ ^ 2 ≤ 1 / μ := by
    have hw1 : w ≤ 1 := by linarith only [hw.2]
    have hw2 : w ^ 2 ≤ 1 := by nlinarith only [hw0, hw1]
    calc
      w ^ 2 / μ ^ 2 ≤ 1 / μ ^ 2 := div_le_div_of_nonneg_right hw2 (sq_nonneg μ)
      _ ≤ 1 / μ := div_le_div_of_nonneg_left (by norm_num) hμ0 (by nlinarith only [hμ])
  refine ⟨?_, ?_, ?_⟩
  · rw [hformula ![1, 0, 0]]
    simp only [Matrix.cons_val_zero, mul_one]
    have HB := connectionExitPhase_radial_error_bound (w := w) hμ hr.1 hr.2.2.1 (J ![1, 0, 0] 0) (J ![1, 0, 0] 2)
    apply HB.trans
    have Hsecond : (4 * (y 2) ^ 2 / μ ^ 2) * |J ![1, 0, 0] 0| ≤ 5 * w ^ 2 / μ ^ 2 := by
      have HB' := mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv2 (by norm_num)) (sq_nonneg μ))
        hzμ (abs_nonneg _) (show 0 ≤ 4 * w ^ 2 / μ ^ 2 by positivity)
      apply HB'.trans
      have hq : 0 ≤ w ^ 2 / μ ^ 2 := by positivity
      simp only [div_eq_mul_inv] at hq ⊢
      nlinarith only [hq]
    have HB' := add_le_add (add_le_add (add_le_add hdμ Hsecond)
      (mul_le_mul_of_nonneg_left hyμ (by norm_num : (0 : ℝ) ≤ 4 / 3))) (le_refl (2 * w ^ 2 / μ ^ 2))
    apply HB'.trans
    have hUq : 0 ≤ u / μ ^ 2 := by positivity
    have hWq : 0 ≤ w ^ 2 / μ ^ 2 := by positivity
    simp only [div_eq_mul_inv] at hUq hWq ⊢
    nlinarith only [hUq, hWq]
  · rw [hformula ![0, 1, 0]]
    simp only [Matrix.cons_val_zero, mul_zero, sub_zero]
    apply (connectionExitPhase_response_bound hμ hr.1 hr.2.2.1 (J ![0, 1, 0] 0) (J ![0, 1, 0] 2)).trans
    apply (mul_le_mul_of_nonneg_left (add_le_add hzU hyU) (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans
    have hi : 0 ≤ 1 / μ := by positivity
    simp only [div_eq_mul_inv] at hsmall hi ⊢
    nlinarith only [hsmall, hi]
  · rw [hformula ![0, 0, 1]]
    simp only [Matrix.cons_val_zero, mul_zero, sub_zero]
    apply (connectionExitPhase_response_bound hμ hr.1 hr.2.2.1 (J ![0, 0, 1] 0) (J ![0, 0, 1] 2)).trans
    apply (mul_le_mul_of_nonneg_left (add_le_add hzW hyW) (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans
    have hUq : 0 ≤ u / μ := by positivity
    have hWq : 0 ≤ w / μ := by positivity
    simp only [div_eq_mul_inv] at hUq hWq ⊢
    nlinarith only [hUq, hWq]
