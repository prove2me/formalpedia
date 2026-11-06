-- Prove2me | solution 1 for BianchiIX.connectionReturn_log_amplitude_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T10:37:29.547832+00:00
-- url     : https://prove2.me/submissions/af364760-25ee-4bda-9df7-3c13be01135a

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
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
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
import Theorems.Thm_BianchiIX_connectionLogField_components
import Theorems.Thm_BianchiIX_connectionReturn_differential
import Theorems.Thm_BianchiIX_connectionReturn_fixed_clock_bounds
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_connection_growing_endpoint_coefficients
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_exists_connection_first_return
import Theorems.Thm_BianchiIX_normalized_wall_sign
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
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

private theorem BianchiIX.connection_strong_rate_le {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000) :
    connectionStrongRate m u v w ≤ -μ ^ 2 / 4 := by
  have hm0 : 7 * μ / 8 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hm2 := mul_nonneg (sub_nonneg.mpr hm0)
    (show 0 ≤ m + 7 * μ / 8 by linarith only [hm0, hμ])
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionStrongRate
  nlinarith only [hm2, hu2, hμ, sq_nonneg (μ - 4), sq_nonneg (v - w)]

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

private theorem BianchiIX.connection_amplitude_base_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |1 + coupling u v w| ≤ 2 ∧ |connectionStrongClockRate m u v w| ≤ 2 * μ ∧
      |m + connectionStrongClockRate m u v w| ≤ 4 * μ ∧ |v + w - 2 * u| ≤ 3 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hm0 : 0 ≤ m := by linarith only [hμ, (abs_le.mp hm).1]
  have hm1 : m ≤ 9 * μ / 8 := by linarith only [hμ, (abs_le.mp hm).2]
  have hm2 := pow_le_pow_left₀ hm0 hm1 2
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hd : |v - w| ≤ 1 := abs_le.mpr ⟨by linarith only [hv.1, hw.2], by linarith only [hv.2, hw.1]⟩
  have hd2 : (v - w) ^ 2 ≤ 1 := by nlinarith only [sq_abs (v - w), pow_le_pow_left₀ (abs_nonneg _) hd 2]
  have hN : |connectionStrongRate m u v w| ≤ μ ^ 2 := by
    have H := connection_strong_rate_le (v := v) (w := w) hμ hm hu
    rw [abs_le]
    dsimp [connectionStrongRate] at *
    constructor <;> nlinarith only [hm2, hd2, sq_nonneg u, sq_nonneg μ, H]
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hD, hμ0]
  have ha : |connectionStrongClockRate m u v w| ≤ 2 * μ := by
    rw [connectionStrongClockRate, abs_div, abs_of_pos hD0]
    apply (div_le_iff₀ hD0).mpr
    have H := mul_le_mul_of_nonneg_left hD hμ0.le
    nlinarith only [hN, H]
  refine ⟨?_, ha, ?_, ?_⟩
  · have hC := connection_coupling_bounds hu.1 hv hw
    apply abs_le.mpr
    constructor <;> nlinarith only [hC.1, hC.2, hu.2, hu2]
  · exact (abs_add_le _ _).trans ((add_le_add (by simpa [abs_of_nonneg hm0] using hm1) ha).trans
      (by linarith only [hμ0]))
  · apply abs_le.mpr
    constructor <;> linarith only [hu.1, hu.2, hv.1, hv.2, hw.1, hw.2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.mul_neg_log_le_one {w : ℝ} (hw : 0 < w) : w * (-Real.log w) ≤ 1 := by
  have H := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hw) hw.le
  have hid : w * (1 - w⁻¹) = w - 1 := by field_simp
  rw [hid] at H
  nlinarith only [H, hw]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_weak_clock_rate_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionWeakClockRate m u v w| ≤ 1 + 8 / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hμ, hD]
  have hC := (connection_amplitude_base_bounds hμ hm hu hv hw).1
  have hq : |2 * (1 + coupling u v w) / connectionSpeed m u v w| ≤ 8 / μ := by
    rw [abs_div, abs_mul, abs_of_pos hD0, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      2 * |1 + coupling u v w| / connectionSpeed m u v w ≤ 4 / connectionSpeed m u v w :=
        div_le_div_of_nonneg_right (by linarith only [hC]) hD0.le
      _ ≤ 4 / (μ / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hD
      _ = 8 / μ := by ring
  exact (abs_sub _ _).trans (by simpa [connectionWeakClockRate] using add_le_add_left hq 1)

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
open Set MeasureTheory

private theorem BianchiIX.connectionShiftedTangent_component_bounds {μ x R : ℝ} {d : Fin 4 → ℝ}
    (hμ : 0 < μ) (hbound : ‖connectionWeightedTangent μ d - ![x, 0]‖ ≤ R) :
    |d 1| ≤ |x| + R ∧ |d 2| ≤ R / μ ^ 2 := by
  have hx : |d 1 - x| ≤ R := by
    simpa [connectionWeightedTangent, Real.norm_eq_abs] using
      (norm_le_pi_norm (connectionWeightedTangent μ d - ![x, 0]) 0).trans hbound
  have hy : μ ^ 2 * |d 2| ≤ R := by
    simpa [connectionWeightedTangent, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg μ)] using
      (norm_le_pi_norm (connectionWeightedTangent μ d - ![x, 0]) 1).trans hbound
  refine ⟨?_, (le_div_iff₀ (sq_pos_of_pos hμ)).mpr (by simpa only [mul_comm] using hy)⟩
  have H : |d 1| ≤ |d 1 - x| + |x| := by simpa using abs_add_le (d 1 - x) x
  linarith only [H, hx]

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

/-- All six ordinary parameter derivatives of the positive-wall first-return log amplitudes. -/
theorem solution {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    let μ := p 0
    let u := p 1
    let w := p 2
    let L := -Real.log w
    let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p
    |J ![1, 0, 0] 1| ≤ 137 * L ∧
    |J ![1, 0, 0] 2| ≤ 137 * L / μ ^ 2 ∧
    |J ![0, 1, 0] 1| ≤ 9000 * (1 / u + L / μ) ∧
    |J ![0, 1, 0] 2| ≤ 9000 * (1 + L) / μ ^ 2 ∧
    |J ![0, 0, 1] 1| ≤ 32 * μ / w ∧
    |J ![0, 0, 1] 2| ≤ (1 + 32 / μ) / w := by
  intro μ u w L J
  let y := connectionEntry μ u w
  let D := connectionLogFlowVariation y 0 (connectionReturnTime p)
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hu0 : 0 < u := hu.1
  have hw0 : 0 < w := hw.1
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hw0.le (by linarith only [hw.2]))
  have hu1 : u ≤ 1 := by
    have H := (le_div_iff₀ hμ0).mp hu.2
    nlinarith only [H, hμ, hu0]
  have hμ1 : 1 ≤ μ := by linarith only [hμ]
  have hrad : J ![1, 0, 0] = D ![-1, 0, 0, 0] := by
    simpa [J, D, y, μ, u, w] using connectionReturn_log_differential hμ hu hw ![1, 0, 0]
  have hstrong : J ![0, 1, 0] = D ![0, 1, 0, 0] := by
    simpa [J, D, y, μ, u, w] using connectionReturn_log_differential hμ hu hw ![0, 1, 0]
  have hgrowing : J ![0, 0, 1] = D ![0, 0, 0, 1] - (1 / w) • connectionLogCoordinateRates (connectionReturnState p) := by
    simpa [J, D, y, μ, u, w] using connectionReturn_log_differential hμ hu hw ![0, 0, 1]
  have H := connectionReturn_fixed_clock_bounds hμ hu hw
  have hradial : |D ![-1, 0, 0, 0] 1| ≤ (2048 / 15) * L ∧
      |D ![-1, 0, 0, 0] 2| ≤ ((2048 / 15) * L) / μ ^ 2 := by
    have Hn : ‖connectionWeightedTangent μ (D ![-1, 0, 0, 0]) - ![(0 : ℝ), 0]‖ ≤ (2048 / 15) * L := by
      have hz : (![(0 : ℝ), 0] : Fin 2 → ℝ) = 0 := by ext i; fin_cases i <;> rfl
      conv_lhs => arg 1; arg 2; rw [hz]
      rw [sub_zero]
      exact H.1.2.2
    simpa using connectionShiftedTangent_component_bounds hμ0 Hn
  have hcoeff := connection_growing_endpoint_coefficients hμ ⟨hu.1.le, hu.2⟩ hw (mul_neg_log_le_one hw0)
  have hg1 : |D ![0, 0, 0, 1] 1| ≤ 16 * μ / w := H.2.2.2.1.trans hcoeff.1
  have hg2 : |D ![0, 0, 0, 1] 2| ≤ 200 / (μ ^ 3 * w) := H.2.2.2.2.trans hcoeff.2
  have hc := connectionReturn_control hμ ⟨hu.1.le, hu.2⟩ hw
  have hr := (hc.2 (connectionReturnTime p) ⟨hc.1.le, le_rfl⟩).2
  change connectionRegion μ (connectionReturnState p) at hr
  have ha : |connectionLogCoordinateRates (connectionReturnState p) 1| ≤ 2 * μ :=
    (connection_amplitude_base_bounds hμ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2).2.1
  have hb : |connectionLogCoordinateRates (connectionReturnState p) 2| ≤ 1 + 8 / μ :=
    connection_weak_clock_rate_bound hμ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  have hcorrection (i : Fin 4) : |J ![0, 0, 1] i| ≤
      |D ![0, 0, 0, 1] i| + |connectionLogCoordinateRates (connectionReturnState p) i| / w := by
    rw [hgrowing]
    have Habs := abs_sub (D ![0, 0, 0, 1] i) ((1 / w) * connectionLogCoordinateRates (connectionReturnState p) i)
    simpa [abs_mul, abs_of_pos hw0, div_eq_mul_inv, mul_comm] using Habs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrad]
    exact hradial.1.trans (by nlinarith only [hL])
  · rw [hrad]
    exact hradial.2.trans (div_le_div_of_nonneg_right (by nlinarith only [hL]) (sq_nonneg μ))
  · rw [hstrong]
    apply H.2.1.2.1.trans
    change 1 / u + 256 + 8960 * L / μ ≤ 9000 * (1 / u + L / μ)
    have hi : 1 ≤ 1 / u := (le_div_iff₀ hu0).mpr (by simpa using hu1)
    have hq : 0 ≤ L / μ := div_nonneg hL hμ0.le
    simp only [div_eq_mul_inv] at hi hq ⊢
    nlinarith only [hi, hq]
  · rw [hstrong]
    apply H.2.1.2.2.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg μ)
    have hq : L / μ ≤ L := (div_le_iff₀ hμ0).mpr (by nlinarith only [hμ1, hL])
    change 256 + 8960 * L / μ ≤ 9000 * (1 + L)
    simp only [div_eq_mul_inv] at hq ⊢
    nlinarith only [hq, hL]
  · apply (hcorrection 1).trans
    apply (add_le_add hg1 (div_le_div_of_nonneg_right ha hw0.le)).trans
    change 16 * μ / w + 2 * μ / w ≤ 32 * μ / w
    have hq : 0 ≤ μ / w := (div_pos hμ0 hw0).le
    simp only [div_eq_mul_inv] at hq ⊢
    nlinarith only [hq]
  · apply (hcorrection 2).trans
    apply (add_le_add hg2 (div_le_div_of_nonneg_right hb hw0.le)).trans
    have hsmall : 200 / μ ^ 3 ≤ 24 / μ := by
      calc
        200 / μ ^ 3 = (200 / μ ^ 2) / μ := by ring
        _ ≤ 24 / μ := div_le_div_of_nonneg_right
          ((div_le_iff₀ (sq_pos_of_pos hμ0)).mpr (by nlinarith only [hμ])) hμ0.le
    calc
      200 / (μ ^ 3 * w) + (1 + 8 / μ) / w = (1 + 8 / μ + 200 / μ ^ 3) / w := by ring
      _ ≤ (1 + 32 / μ) / w := div_le_div_of_nonneg_right (by
        simp only [div_eq_mul_inv] at hsmall ⊢
        linarith only [hsmall]) hw0.le
