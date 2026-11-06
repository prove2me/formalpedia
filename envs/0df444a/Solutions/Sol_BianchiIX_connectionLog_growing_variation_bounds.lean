-- Prove2me | solution 1 for BianchiIX.connectionLog_growing_variation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T10:09:54.04573+00:00
-- url     : https://prove2.me/submissions/aa0a2ee9-60c6-4a18-90ff-a1624618ebb4

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseLinearization
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Analysis_ConnectionLogLinearization
import Definitions.Def_BianchiIX_Analysis_ConnectionFeedbackBounds
import Definitions.Def_BianchiIX_Analysis_ConnectionGrowingSources
import Definitions.Def_BianchiIX_Analysis_ConnectionGrowingFeedbackBounds
import Theorems.Thm_BianchiIX_abs_bounds_of_forced_derivative_feedback
import Theorems.Thm_BianchiIX_connectionLogField_components
import Theorems.Thm_BianchiIX_connectionLog_growing_moments
import Theorems.Thm_BianchiIX_connectionLog_growing_transverse_bounds
import Theorems.Thm_BianchiIX_connectionLog_prefix_estimates
import Theorems.Thm_BianchiIX_connectionPhaseGPartials_bounds
import Theorems.Thm_BianchiIX_connectionStrongClockPartials_bounds
import Theorems.Thm_BianchiIX_connectionWeakClockPartials_bounds
import Theorems.Thm_BianchiIX_connection_weak_clock_rates
import Theorems.Thm_BianchiIX_integral_le_of_dissipation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
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
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.ProjIcc

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_moments_le_of_linear_dissipation {f f' : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hdecay : ∀ t ∈ Icc a b, f' t ≤ -c * f t) (hfb : 0 ≤ f b) :
    (∫ t in a..b, f t) ≤ f a / c ∧ (∫ t in a..b, (t - a) * f t) ≤ f a / c ^ 2 := by
  have hcont := HasDerivAt.continuousOn hf
  refine ⟨integral_le_of_dissipation hab hc hf hcont hdecay hfb, ?_⟩
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => (1 + c * (s - a)) * f s)
        (c * f t + (1 + c * (t - a)) * f' t) t := by
    convert! ((((hasDerivAt_id t).sub_const a).const_mul c).const_add 1).mul (hf t ht) using 1
    simp
  have H := integral_le_of_dissipation (g := fun t => (t - a) * f t) hab (sq_pos_of_pos hc) hd
    ((continuousOn_id.sub continuousOn_const).mul hcont) (fun t ht => ?_) ?_
  · simpa only [sub_self, mul_zero, add_zero, one_mul] using H
  · have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have hfactor : 0 ≤ 1 + c * (t - a) := by positivity
    have H' := mul_le_mul_of_nonneg_left (hdecay t ht) hfactor
    nlinarith only [H']
  · exact mul_nonneg (by positivity) hfb

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

private theorem BianchiIX.connection_coupling_nonneg {u v w : ℝ}
    (hu : 0 ≤ u) (hw : 0 ≤ w) (huv : u ≤ v) : 0 ≤ coupling u v w := by
  unfold coupling
  exact mul_nonneg hu (by linarith only [hw, huv])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_strong_clock_rate_le {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (huv : u ≤ v) :
    connectionStrongRate m u v w / connectionSpeed m u v w ≤ -μ / 2 := by
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hDpos : 0 < connectionSpeed m u v w := by linarith only [hD, hμ]
  have hc := connection_coupling_nonneg hu.1 hw.1 huv
  have hm0 : 0 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hprod := mul_nonneg (show 0 ≤ m - μ + 1 / 2 by linarith only [(abs_le.mp hm).1]) hm0
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  apply (div_le_iff₀ hDpos).mpr
  dsimp [connectionStrongRate, connectionSpeed]
  nlinarith only [hprod, hu2, (abs_le.mp hm).2, hμ, sq_nonneg (v - w),
    mul_nonneg (show 0 ≤ μ by linarith only [hμ]) hc]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.hasDerivAt_connectionLog_product {Y : ℝ → ProjectiveState} {z : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y z)) z) (hD : connectionClockRate (Y z) ≠ 0) :
    HasDerivAt (fun t => Y t 2 * Y t 3)
      ((-2 * (1 + coupling (Y z 1) (Y z 2) (Y z 3)) / connectionClockRate (Y z)) * (Y z 2 * Y z 3)) z := by
  have H := (hasDerivAt_pi.mp hY 2).mul (hasDerivAt_pi.mp hY 3)
  rw [(connectionLogField_components hD).2.2.1, (connectionLogField_components hD).2.2.2] at H
  convert! H using 1
  dsimp [connectionClockRate, connectionSpeed] at *
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionLog_dissipative_moments {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    (∫ z in a..b, Y z 1) ≤ 2 * Y a 1 / μ ∧
      (∫ z in a..b, (z - a) * Y z 1) ≤ 4 * Y a 1 / μ ^ 2 ∧
      (∫ z in a..b, (Y z 2 * Y z 3) ^ 2) ≤ μ * (Y a 2 * Y a 3) ^ 2 / 4 ∧
      (∫ z in a..b, (z - a) * (Y z 2 * Y z 3) ^ 2) ≤ μ ^ 2 * (Y a 2 * Y a 3) ^ 2 / 16 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hv' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ Y z 2 ∧ Y z 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
  have hD (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) (hv' z hz) (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  have hU (z : ℝ) (hz : z ∈ Icc a b) : connectionLogField (Y z) 1 ≤ -(μ / 2) * Y z 1 := by
    rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.1]
    simpa only [neg_div, connectionClockRate, connectionSpeed] using mul_le_mul_of_nonneg_right
      (connection_strong_clock_rate_le hμ (hm z hz) (hu z hz) (hv' z hz) (hw z hz) (huv z hz)) (hu z hz).1
  have HU := integral_moments_le_of_linear_dissipation hab (by positivity : 0 < μ / 2)
    (fun z hz => hasDerivAt_pi.mp (hY z hz) 1) hU (hu b ⟨hab, le_rfl⟩).1
  have HP := integral_moments_le_of_linear_dissipation hab (by positivity : 0 < 4 / μ)
    (fun z hz => (hasDerivAt_connectionLog_product (hY z hz) (ne_of_gt (hD z hz))).pow 2)
    (fun z hz => ?_) (sq_nonneg (Y b 2 * Y b 3))
  · refine ⟨HU.1.trans_eq (by ring), HU.2.trans_eq (by ring), HP.1.trans_eq ?_, HP.2.trans_eq ?_⟩
    · simp only [Pi.pow_apply]
      field_simp
    · simp only [Pi.pow_apply]
      field_simp
      norm_num
  · have H := mul_le_mul_of_nonneg_right
      (connection_weak_clock_rates hμ (hm z hz) (hu z hz) (hv' z hz) (hw z hz) (huv z hz)).2
      (by positivity : 0 ≤ 2 * (Y z 2 * Y z 3) ^ 2)
    simp only [Pi.pow_apply, connectionClockRate]
    convert! H using 1 <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseFeedbackRate_nonneg {μ τ u p : ℝ} (hμ : 0 ≤ μ) (hτ : 0 ≤ τ) (hu : 0 ≤ u) :
    0 ≤ connectionPhaseFeedbackRate μ τ u p := by
  unfold connectionPhaseFeedbackRate
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseFeedbackBudget_small {μ u p : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hp : 0 ≤ p ∧ p ≤ 1 / 10000) :
    connectionPhaseFeedbackBudget μ u p ≤ 1 / 16 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hμ3 : 64 ≤ μ ^ 3 := by nlinarith only [mul_le_mul_of_nonneg_right hμ2 hμ0.le, hμ]
  have hu' : u ≤ 1 / 40000 := hu.2.trans
    ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 10000) (by norm_num : (0 : ℝ) < 4) hμ).trans_eq (by norm_num))
  have hp2 : p ^ 2 ≤ 1 / 100000000 := by nlinarith only [hp.1, hp.2, mul_nonneg hp.1 (sub_nonneg.mpr hp.2)]
  have H1 : u / μ ^ 3 ≤ 1 / 2560000 :=
    (div_le_div_of_nonneg_right hu' (by positivity)).trans
      ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 40000) (by norm_num : (0 : ℝ) < 64) hμ3).trans_eq (by norm_num))
  have H2 : u / μ ^ 2 ≤ 1 / 640000 :=
    (div_le_div_of_nonneg_right hu' (by positivity)).trans
      ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 40000) (by norm_num : (0 : ℝ) < 16) hμ2).trans_eq (by norm_num))
  have H3 : p ^ 2 / μ ^ 3 ≤ 1 / 6400000000 :=
    (div_le_div_of_nonneg_right hp2 (by positivity)).trans
      ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 100000000) (by norm_num : (0 : ℝ) < 64) hμ3).trans_eq (by norm_num))
  have hid : connectionPhaseFeedbackBudget μ u p = 128 * (u / μ ^ 3) +
      32768 * (u / μ ^ 2) + 528 * (p ^ 2 / μ ^ 3) := by unfold connectionPhaseFeedbackBudget; ring
  rw [hid]
  linarith only [H1, H2, H3]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhase_transverse_row_bound {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) :
    |connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3) 1| +
      |connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3) 2| / μ ^ 2 ≤
        64 * (y 1 + (y 2 * y 3) ^ 2 / μ ^ 5) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ2 : 1 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hG := connectionPhaseGPartials_bounds hμ hm hu hv hw
  have huv : y 1 * y 2 / μ ^ 2 ≤ y 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hμ0)).mpr
    exact (mul_le_mul_of_nonneg_left hv.2 hu.1).trans
      (by simpa using mul_le_mul_of_nonneg_left hμ2 hu.1)
  have H := add_le_add hG.2.1 (div_le_div_of_nonneg_right hG.2.2.1 (sq_nonneg μ))
  have hid : 32 * (y 1 * y 2 + (y 2 * y 3) ^ 2 / μ ^ 3) / μ ^ 2 =
      32 * (y 1 * y 2 / μ ^ 2) + 32 * ((y 2 * y 3) ^ 2 / μ ^ 5) := by field_simp
  rw [hid] at H
  have hp : 0 ≤ (y 2 * y 3) ^ 2 / μ ^ 5 := by positivity
  linarith only [H, huv, hp]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_connectionPhaseFeedbackRate {U P : ℝ → ℝ} {μ a b : ℝ} (hab : a ≤ b)
    (hU : ContinuousOn U (Icc a b)) (hP : ContinuousOn P (Icc a b)) :
    (∫ z in a..b, connectionPhaseFeedbackRate μ (z - a) (U z) (P z)) =
      (64 / μ ^ 2) * (∫ z in a..b, U z) + (64 / μ ^ 4) * (∫ z in a..b, P z ^ 2) +
      8192 * (∫ z in a..b, (z - a) * U z) + (8192 / μ ^ 5) * ∫ z in a..b, (z - a) * P z ^ 2 := by
  have htime : ContinuousOn (fun z : ℝ => z - a) (Icc a b) := continuousOn_id.sub continuousOn_const
  have h1 := (hU.const_mul (64 / μ ^ 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have h2 := ((hP.pow 2).const_mul (64 / μ ^ 4)).intervalIntegrable_of_Icc (μ := volume) hab
  have h3 := ((htime.mul hU).const_mul 8192).intervalIntegrable_of_Icc (μ := volume) hab
  have h4 := ((htime.mul (hP.pow 2)).const_mul (8192 / μ ^ 5)).intervalIntegrable_of_Icc (μ := volume) hab
  simp only [Pi.pow_apply, Pi.mul_apply] at h2 h3 h4
  have heq (z : ℝ) : connectionPhaseFeedbackRate μ (z - a) (U z) (P z) =
      (64 / μ ^ 2) * U z + (64 / μ ^ 4) * P z ^ 2 + 8192 * ((z - a) * U z) +
        (8192 / μ ^ 5) * ((z - a) * P z ^ 2) := by unfold connectionPhaseFeedbackRate; ring
  simp_rw [heq]
  rw [intervalIntegral.integral_add ((h1.add h2).add h3) h4,
    intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionLog_feedback_budget {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000) :
    (∫ z in a..b, connectionPhaseFeedbackRate μ (z - a) (Y z 1) (Y z 2 * Y z 3)) ≤
      connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3) ∧
      connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3) ≤ 1 / 16 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hc := HasDerivAt.continuousOn hY
  have hU := continuousOn_pi.mp hc 1
  have hP : ContinuousOn (fun z => Y z 2 * Y z 3) (Icc a b) :=
    (continuousOn_pi.mp hc 2).mul (continuousOn_pi.mp hc 3)
  have H := connectionLog_dissipative_moments hab hμ hY hm hu hv hw hentry
  constructor
  · rw [integral_connectionPhaseFeedbackRate (μ := μ) hab hU hP]
    apply (add_le_add (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left H.1 (by positivity : 0 ≤ 64 / μ ^ 2))
        (mul_le_mul_of_nonneg_left H.2.2.1 (by positivity : 0 ≤ 64 / μ ^ 4)))
      (mul_le_mul_of_nonneg_left H.2.1 (by norm_num : (0 : ℝ) ≤ 8192)))
      (mul_le_mul_of_nonneg_left H.2.2.2 (by positivity : 0 ≤ 8192 / μ ^ 5))).trans_eq
    unfold connectionPhaseFeedbackBudget
    field_simp
    ring
  · have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
    apply connectionPhaseFeedbackBudget_small hμ ⟨(hu a ha).1, hsmall⟩
    refine ⟨mul_nonneg (hv a ha).1.le (hw a ha).1, ?_⟩
    exact (mul_le_mul_of_nonneg_right (hv a ha).2 (hw a ha).1).trans (by simpa using hwall)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.continuous_connectionGrowingSources (μ w : ℝ) :
    Continuous (connectionGrowingStrongSource μ w) ∧ Continuous (connectionGrowingWeakSource μ w) ∧
      Continuous (connectionGrowingPhaseSource μ w) := by
  unfold connectionGrowingStrongSource connectionGrowingWeakSource connectionGrowingPhaseSource
  exact ⟨by fun_prop, by fun_prop, by fun_prop⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionGrowingSources_bound {μ w : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ) (hw0 : 0 < w)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) :
    |connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w| ≤ connectionGrowingStrongSource μ w y ∧
      |μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w| ≤ connectionGrowingWeakSource μ w y ∧
      |connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3) 3 / w| ≤ connectionGrowingPhaseSource μ w y := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  simp only [abs_div, abs_of_pos hw0]
  refine ⟨div_le_div_of_nonneg_right (connectionStrongClockPartials_bounds hμ hm hu hv hw).2.2.2 hw0.le,
    ?_, div_le_div_of_nonneg_right (connectionPhaseGPartials_bounds hμ hm hu hv hw).2.2.2 hw0.le⟩
  rw [abs_mul, abs_of_nonneg (sq_nonneg μ)]
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (connectionWeakClockPartials_bounds hμ hm hu hv hw).2.2.2 (sq_nonneg μ)) hw0.le).trans_eq
  unfold connectionGrowingWeakSource
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhase_growing_variation_bound {μ w A B : ℝ} {y : ProjectiveState}
    (hμ : 4 ≤ μ) (hw0 : 0 < w)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1)
    (d : Fin 4 → ℝ) (hζ : d 3 = 1 / w) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : |d 1| ≤ A + B) (hy : |d 2| ≤ B / μ ^ 2) :
    |connectionLogLinearizedRates y d 0| ≤
      64 * (y 1 / μ ^ 2 + (y 2 * y 3) ^ 2 / μ ^ 4) * |d 0| + 32 * y 1 * A +
      64 * (y 1 + (y 2 * y 3) ^ 2 / μ ^ 5) * B + connectionGrowingPhaseSource μ w y := by
  let G := connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3)
  have hsum : |connectionLogLinearizedRates y d 0| ≤
      |G 0| * |d 0| + |G 1| * |d 1| + |G 2| * |d 2| + |G 3| * |d 3| := by
    change |∑ j : Fin 4, G j * d j| ≤ _
    simpa [Fin.sum_univ_succ, abs_mul, add_assoc] using Finset.abs_sum_le_sum_abs (fun j : Fin 4 => G j * d j) Finset.univ
  have hwall : |G 3| * |d 3| ≤ connectionGrowingPhaseSource μ w y := by
    simpa [G, hζ, abs_div, div_eq_mul_inv] using (connectionGrowingSources_bound hμ hw0 hm hu hv hw).2.2
  have H := hsum.trans (add_le_add (add_le_add (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left hx (abs_nonneg _))) (mul_le_mul_of_nonneg_left hy (abs_nonneg _))) hwall)
  have hG := connectionPhaseGPartials_bounds hμ hm hu hv hw
  have hT := connectionPhase_transverse_row_bound hμ hm hu hv hw
  calc
    _ ≤ |G 0| * |d 0| + |G 1| * A + (|G 1| + |G 2| / μ ^ 2) * B + connectionGrowingPhaseSource μ w y :=
      H.trans_eq (by ring)
    _ ≤ _ := add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right hG.1 (abs_nonneg _)) (mul_le_mul_of_nonneg_right hG.2.1 hA))
      (mul_le_mul_of_nonneg_right hT hB)) (le_refl _)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.continuous_connectionGrowingFeedbackSource (μ u w : ℝ) :
    Continuous (connectionGrowingFeedbackSource μ u w) := by
  unfold connectionGrowingFeedbackSource connectionGrowingPhaseSource
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionGrowingFeedbackSource_nonneg {μ u w : ℝ} {y : ProjectiveState}
    (hμ : 0 ≤ μ) (hu : 0 ≤ u) (hw : 0 ≤ w) (hU : 0 ≤ y 1) (hW : 0 ≤ y 3) :
    0 ≤ connectionGrowingFeedbackSource μ u w y := by
  unfold connectionGrowingFeedbackSource connectionGrowingPhaseSource
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionGrowingFeedbackBudget_small {μ u w : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    2 * w / μ + connectionGrowingFeedbackBudget μ u w ≤ 7500 * (u + w) / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ3 : 64 ≤ μ ^ 3 := by
    have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hμ 3
    norm_num at H
    exact H
  have hμ5 : 1024 ≤ μ ^ 5 := by
    have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hμ 5
    norm_num at H
    exact H
  have hu' : u ≤ 1 / 40000 := hu.2.trans
    ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 10000) (by norm_num : (0 : ℝ) < 4) hμ).trans_eq (by norm_num))
  have hw2 : w ^ 2 ≤ 1 / 100000000 := by
    have H := pow_le_pow_left₀ hw.1 hw.2 2
    norm_num at H
    exact H
  have Hw : 204800 * w ^ 2 / μ ^ 3 ≤ 1 := (div_le_iff₀ (by positivity : 0 < μ ^ 3)).mpr
    (by linarith only [hw2, hμ3])
  have Hμ5 : 2048 / μ ^ 5 ≤ (2 : ℝ) := (div_le_iff₀ (by positivity : 0 < μ ^ 5)).mpr (by linarith only [hμ5])
  have Hμ : 8 / μ ≤ (2 : ℝ) := (div_le_iff₀ hμ0).mpr (by linarith only [hμ])
  have HU := mul_le_mul_of_nonneg_left
    (show 7296 + 1638400 * u + 204800 * w ^ 2 / μ ^ 3 ≤ 7500 by linarith only [hu', Hw]) hu.1
  have HW := mul_le_mul_of_nonneg_left
    (show 2048 / μ ^ 5 + 8 / μ + 2 ≤ (7500 : ℝ) by linarith only [Hμ5, Hμ]) hw.1
  calc
    _ = (u * (7296 + 1638400 * u + 204800 * w ^ 2 / μ ^ 3) + w * (2048 / μ ^ 5 + 8 / μ + 2)) / μ := by
      unfold connectionGrowingFeedbackBudget
      ring
    _ ≤ (u * 7500 + w * 7500) / μ := div_le_div_of_nonneg_right (add_le_add HU HW) hμ0.le
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_connectionGrowingSources {Y : ℝ → ProjectiveState} {μ w a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b)) :
    (∫ z in a..b, connectionGrowingStrongSource μ w (Y z)) =
      (32 / (μ * w)) * ((∫ z in a..b, Y z 3 ^ 2) + ∫ z in a..b, Y z 2 * Y z 3) +
        (32 / w) * (∫ z in a..b, Y z 1 * Y z 3) ∧
    (∫ z in a..b, connectionGrowingWeakSource μ w (Y z)) =
      (64 / (μ * w)) * (∫ z in a..b, Y z 3 ^ 2) + (64 * μ / w) * (∫ z in a..b, Y z 1 * Y z 3) ∧
    (∫ z in a..b, connectionGrowingPhaseSource μ w (Y z)) =
      (32 / w) * (∫ z in a..b, Y z 1 * Y z 3) +
        (32 / (μ ^ 3 * w)) * (∫ z in a..b, (Y z 2 * Y z 3) ^ 2) := by
  have hW : IntervalIntegrable (fun z => Y z 3 ^ 2) volume a b :=
    ((continuousOn_pi.mp hc 3).pow 2).intervalIntegrable_of_Icc hab
  have hP : IntervalIntegrable (fun z => Y z 2 * Y z 3) volume a b :=
    ((continuousOn_pi.mp hc 2).mul (continuousOn_pi.mp hc 3)).intervalIntegrable_of_Icc hab
  have hUW : IntervalIntegrable (fun z => Y z 1 * Y z 3) volume a b :=
    ((continuousOn_pi.mp hc 1).mul (continuousOn_pi.mp hc 3)).intervalIntegrable_of_Icc hab
  have hP2 : IntervalIntegrable (fun z => (Y z 2 * Y z 3) ^ 2) volume a b :=
    (((continuousOn_pi.mp hc 2).mul (continuousOn_pi.mp hc 3)).pow 2).intervalIntegrable_of_Icc hab
  have hadd (f g : ℝ → ℝ) (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
      (c d : ℝ) : (∫ z in a..b, c * f z + d * g z) = c * (∫ z in a..b, f z) + d * ∫ z in a..b, g z := by
    rw [intervalIntegral.integral_add (hf.const_mul c) (hg.const_mul d)]
    simp only [intervalIntegral.integral_const_mul]
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = ∫ z in a..b, (32 / (μ * w)) * (Y z 3 ^ 2 + Y z 2 * Y z 3) + (32 / w) * (Y z 1 * Y z 3) := by
        apply intervalIntegral.integral_congr
        intro z _
        unfold connectionGrowingStrongSource
        ring
      _ = _ := by rw [hadd _ _ (hW.add hP) hUW, intervalIntegral.integral_add hW hP]
  · calc
      _ = ∫ z in a..b, (64 / (μ * w)) * Y z 3 ^ 2 + (64 * μ / w) * (Y z 1 * Y z 3) := by
        apply intervalIntegral.integral_congr
        intro z _
        unfold connectionGrowingWeakSource
        ring
      _ = _ := hadd _ _ hW hUW _ _
  · calc
      _ = ∫ z in a..b, (32 / w) * (Y z 1 * Y z 3) + (32 / (μ ^ 3 * w)) * (Y z 2 * Y z 3) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro z _
        unfold connectionGrowingPhaseSource
        ring
      _ = _ := hadd _ _ hUW hP2 _ _

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionLog_growing_source_integrals {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hw0 : 0 < Y a 3) :
    (∫ z in a..b, connectionGrowingStrongSource μ (Y a 3) (Y z)) ≤
      32 * (1 + Y b 3 ^ 2 / (μ * Y a 3)) ∧
    (∫ z in a..b, connectionGrowingWeakSource μ (Y a 3) (Y z)) ≤
      256 * Y a 1 + 32 * Y b 3 ^ 2 / (μ * Y a 3) ∧
    (∫ z in a..b, connectionGrowingPhaseSource μ (Y a 3) (Y z)) ≤
      128 * Y a 1 / μ + 8 * Y a 3 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hc := HasDerivAt.continuousOn hY
  have HI := integral_connectionGrowingSources (μ := μ) (w := Y a 3) hab hc
  have HM := connectionLog_growing_moments hab hμ hY hm hu hv hw hentry
  have HP := (connectionLog_dissipative_moments hab hμ hY hm hu hv hw hentry).2.2.1
  rw [HI.1, HI.2.1, HI.2.2]
  refine ⟨?_, ?_, ?_⟩
  · have H := add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add HM.1 HM.2.2.2.1) (by positivity : 0 ≤ 32 / (μ * Y a 3)))
      (mul_le_mul_of_nonneg_left HM.2.1 (by positivity : 0 ≤ 32 / Y a 3))
    have hid : (32 / (μ * Y a 3)) * (Y b 3 ^ 2 / 2 + μ * (Y a 2 * Y a 3) / 2) +
        (32 / Y a 3) * (4 * Y a 1 * Y a 3 / μ) =
          16 * (Y b 3 ^ 2 / (μ * Y a 3)) + 16 * Y a 2 + 128 * Y a 1 / μ := by field_simp; ring
    rw [hid] at H
    have huμ : 128 * Y a 1 / μ ≤ 1 := (div_le_iff₀ hμ0).mpr (by linarith only [(hu a ha).2, hμ])
    have hq : 0 ≤ Y b 3 ^ 2 / (μ * Y a 3) := by positivity
    linarith only [H, huμ, (hv a ha).2, hq]
  · apply (add_le_add (mul_le_mul_of_nonneg_left HM.1 (by positivity : 0 ≤ 64 / (μ * Y a 3)))
      (mul_le_mul_of_nonneg_left HM.2.1 (by positivity : 0 ≤ 64 * μ / Y a 3))).trans_eq
    field_simp
    ring
  · have H := add_le_add (mul_le_mul_of_nonneg_left HM.2.1 (by positivity : 0 ≤ 32 / Y a 3))
      (mul_le_mul_of_nonneg_left HP (by positivity : 0 ≤ 32 / (μ ^ 3 * Y a 3)))
    have hid : (32 / Y a 3) * (4 * Y a 1 * Y a 3 / μ) +
        (32 / (μ ^ 3 * Y a 3)) * (μ * (Y a 2 * Y a 3) ^ 2 / 4) =
          128 * Y a 1 / μ + (8 * Y a 3 / μ ^ 2) * Y a 2 ^ 2 := by field_simp; ring
    rw [hid] at H
    have hv2 : Y a 2 ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (hv a ha).1.le (hv a ha).2 2
    exact H.trans (add_le_add (le_refl _)
      ((mul_le_mul_of_nonneg_left hv2 (by positivity : 0 ≤ 8 * Y a 3 / μ ^ 2)).trans_eq (mul_one _)))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_connectionGrowingFeedbackSource {Y : ℝ → ProjectiveState} {μ u w a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b)) :
    (∫ z in a..b, connectionGrowingFeedbackSource μ u w (Y z)) =
      (1024 + 819200 * u) * (∫ z in a..b, Y z 1) +
      (5120 / (μ * w)) * (∫ z in a..b, Y z 1 * Y z 3 ^ 2) +
      (819200 * u / μ ^ 5) * (∫ z in a..b, (Y z 2 * Y z 3) ^ 2) +
      (4096 / (μ ^ 6 * w)) * (∫ z in a..b, (Y z 2 * Y z 3) ^ 2 * Y z 3 ^ 2) +
      (∫ z in a..b, connectionGrowingPhaseSource μ w (Y z)) := by
  have hcoord (i : Fin 4) := continuousOn_pi.mp hc i
  have hU : ContinuousOn (fun z => Y z 1) (Icc a b) := hcoord 1
  have hW : ContinuousOn (fun z => Y z 3 ^ 2) (Icc a b) := (hcoord 3).pow 2
  have hP : ContinuousOn (fun z => (Y z 2 * Y z 3) ^ 2) (Icc a b) := ((hcoord 2).mul (hcoord 3)).pow 2
  have h1 : IntervalIntegrable (fun z => (1024 + 819200 * u) * Y z 1) volume a b :=
    (hU.const_mul _).intervalIntegrable_of_Icc hab
  have h2 : IntervalIntegrable (fun z => (5120 / (μ * w)) * (Y z 1 * Y z 3 ^ 2)) volume a b :=
    ((hU.mul hW).const_mul _).intervalIntegrable_of_Icc hab
  have h3 : IntervalIntegrable (fun z => (819200 * u / μ ^ 5) * (Y z 2 * Y z 3) ^ 2) volume a b :=
    (hP.const_mul _).intervalIntegrable_of_Icc hab
  have h4 : IntervalIntegrable (fun z => (4096 / (μ ^ 6 * w)) * ((Y z 2 * Y z 3) ^ 2 * Y z 3 ^ 2)) volume a b :=
    ((hP.mul hW).const_mul _).intervalIntegrable_of_Icc hab
  have h5 : IntervalIntegrable (fun z => connectionGrowingPhaseSource μ w (Y z)) volume a b :=
    ((continuous_connectionGrowingSources μ w).2.2.comp_continuousOn hc).intervalIntegrable_of_Icc hab
  have hid (z : ℝ) : connectionGrowingFeedbackSource μ u w (Y z) =
      (1024 + 819200 * u) * Y z 1 + (5120 / (μ * w)) * (Y z 1 * Y z 3 ^ 2) +
      (819200 * u / μ ^ 5) * (Y z 2 * Y z 3) ^ 2 +
      (4096 / (μ ^ 6 * w)) * ((Y z 2 * Y z 3) ^ 2 * Y z 3 ^ 2) + connectionGrowingPhaseSource μ w (Y z) := by
    unfold connectionGrowingFeedbackSource
    ring
  simp_rw [hid]
  rw [intervalIntegral.integral_add (((h1.add h2).add h3).add h4) h5,
    intervalIntegral.integral_add ((h1.add h2).add h3) h4,
    intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionLog_growing_feedback_source_budget {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hw0 : 0 < Y a 3) :
    (∫ z in a..b, connectionGrowingFeedbackSource μ (Y a 1) (Y a 3) (Y z)) ≤
      connectionGrowingFeedbackBudget μ (Y a 1) (Y a 3) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hu0 := (hu a ha).1
  have HV : Y a 2 ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ (hv a ha).1.le (hv a ha).2 2
  have HW : Y b 3 ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ (hw b hb).1 (hw b hb).2 2
  have HP : (Y a 2 * Y a 3) ^ 2 ≤ Y a 3 ^ 2 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_right HV (sq_nonneg _)).trans_eq (one_mul _)
  have HM := connectionLog_growing_moments hab hμ hY hm hu hv hw hentry
  have HD := connectionLog_dissipative_moments hab hμ hY hm hu hv hw hentry
  have Hsource := (connectionLog_growing_source_integrals hab hμ hY hm hu hv hw hentry hw0).2.2
  have HP2 : (∫ z in a..b, (Y z 2 * Y z 3) ^ 2) ≤ μ * Y a 3 ^ 2 / 4 :=
    HD.2.2.1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left HP hμ0.le) (by norm_num))
  have HPW : (∫ z in a..b, (Y z 2 * Y z 3) ^ 2 * Y z 3 ^ 2) ≤ Y a 3 ^ 2 / 2 := by
    apply HM.2.2.2.2.trans
    exact div_le_div_of_nonneg_right
      ((mul_le_mul HP HW (sq_nonneg _) (sq_nonneg _)).trans_eq (mul_one _)) (by norm_num)
  rw [integral_connectionGrowingFeedbackSource hab (HasDerivAt.continuousOn hY)]
  apply (add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left HD.1 (by positivity : 0 ≤ 1024 + 819200 * Y a 1))
    (mul_le_mul_of_nonneg_left HM.2.2.1 (by positivity : 0 ≤ 5120 / (μ * Y a 3))))
    (mul_le_mul_of_nonneg_left HP2 (by positivity : 0 ≤ 819200 * Y a 1 / μ ^ 5)))
    (mul_le_mul_of_nonneg_left HPW (by positivity : 0 ≤ 4096 / (μ ^ 6 * Y a 3)))) Hsource).trans_eq
  unfold connectionGrowingFeedbackBudget
  field_simp
  ring

end
end

theorem solution {Y : ℝ → ProjectiveState} {D : ℝ → (Fin 4 → ℝ)}
    {μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hw0 : 0 < Y a 3)
    (hD : ∀ z ∈ Icc a b, HasDerivAt D (connectionLogLinearizedRates (Y z) (D z)) z)
    (hζ : ∀ z ∈ Icc a b, D z 3 = 1 / Y a 3) (hx0 : D a 1 = 0) (hy0 : D a 2 = 0)
    (hJ0 : |D a 0| ≤ 2 * Y a 3 / μ) :
    ∀ t ∈ Icc a b, |D t 0| ≤ 8000 * (Y a 1 + Y a 3) / μ ∧
      |D t 1| ≤ 32 + 12800 * Y a 1 + 96 * Y t 3 ^ 2 / (μ * Y a 3) +
        1024000 * (t - a) * (Y a 1 + Y a 3) / μ ∧
      |D t 2| ≤ (12800 * Y a 1 + 64 * Y t 3 ^ 2 / (μ * Y a 3) +
        1024000 * (t - a) * (Y a 1 + Y a 3) / μ) / μ ^ 2 := by
  let q : ℝ → ℝ := fun z => Y z 3 ^ 2 / (μ * Y a 3)
  let k : ℝ → ℝ := fun z => connectionPhaseFeedbackRate μ (z - a) (Y z 1) (Y z 2 * Y z 3)
  let e : ℝ → ℝ := fun z => connectionGrowingFeedbackSource μ (Y a 1) (Y a 3) (Y z)
  let Λ := connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3)
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hu0 := (hu a ⟨le_rfl, hab⟩).1
  have hcY := HasDerivAt.continuousOn hY
  have hcD := HasDerivAt.continuousOn hD
  have hcoords (i : Fin 4) := continuousOn_pi.mp hcY i
  have hk : ContinuousOn k (Icc a b) := by dsimp [k, connectionPhaseFeedbackRate]; fun_prop
  have hk0 (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ k z :=
    connectionPhaseFeedbackRate_nonneg hμ0.le (sub_nonneg.mpr hz.1) (hu z hz).1
  have he : ContinuousOn e (Icc a b) :=
    (continuous_connectionGrowingFeedbackSource μ (Y a 1) (Y a 3)).comp_continuousOn hcY
  have he0 (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ e z :=
    connectionGrowingFeedbackSource_nonneg hμ0.le hu0 hw0.le (hu z hz).1 (hw z hz).1
  have hbudget := connectionLog_feedback_budget hab hμ hY hm hu hv hw hentry hsmall hwall
  have hΛ : Λ < 1 := hbudget.2.trans_lt (by norm_num)
  have hsource : |D a 0| + (∫ z in a..b, e z) ≤ 7500 * (Y a 1 + Y a 3) / μ :=
    (add_le_add hJ0 (connectionLog_growing_feedback_source_budget hab hμ hY hm hu hv hw hentry hw0)).trans
      (connectionGrowingFeedbackBudget_small hμ ⟨hu0, hsmall⟩ ⟨hw0.le, hwall⟩)
  have htrans := connectionLog_growing_transverse_bounds hab hμ hY hm hu hv hw hentry hsmall hwall hw0 hD hζ hx0 hy0
  have hcap (Q : ℝ) (hQ : ∀ z ∈ Icc a b, |D z 0| ≤ Q) (z : ℝ) (hz : z ∈ Icc a b) :
      |D z 1| ≤ 32 * (1 + q z) + (12800 * Y a 1 + 64 * q z + 128 * (z - a) * Q) ∧
      |D z 2| ≤ (12800 * Y a 1 + 64 * q z + 128 * (z - a) * Q) / μ ^ 2 := by
    have hsub : Icc a z ⊆ Icc a b := Icc_subset_Icc_right hz.2
    have HI := intervalIntegral.integral_mono_on (μ := volume) hz.1
      (((continuousOn_pi.mp hcD 0).abs.mono hsub).intervalIntegrable_of_Icc hz.1)
      (intervalIntegrable_const (c := Q)) (fun r hr => hQ r (hsub hr))
    rw [intervalIntegral.integral_const, smul_eq_mul] at HI
    have H := mul_le_mul_of_nonneg_left HI (by norm_num : (0 : ℝ) ≤ 128)
    refine ⟨(htrans z hz).1.trans ((add_le_add (le_refl _) H).trans_eq (by dsimp [q]; ring)), ?_⟩
    exact (htrans z hz).2.trans ((div_le_div_of_nonneg_right (add_le_add (le_refl _) H) (sq_nonneg μ)).trans_eq (by dsimp [q]; ring))
  have H := abs_bounds_of_forced_derivative_feedback (f := fun z => D z 0) (k := k) (e := e) (Λ := Λ)
    hab (fun z hz => hasDerivAt_pi.mp (hD z hz) 0) hk hk0 he he0 hbudget.1 hΛ (fun Q hQ0 hQ z hz => ?_)
  · have hfinal (z : ℝ) (hz : z ∈ Icc a b) : |D z 0| ≤ 8000 * (Y a 1 + Y a 3) / μ := by
      apply (H z hz).1.trans
      calc
        _ ≤ (7500 * (Y a 1 + Y a 3) / μ) / (1 - Λ) := div_le_div_of_nonneg_right hsource (sub_pos.mpr hΛ).le
        _ ≤ (7500 * (Y a 1 + Y a 3) / μ) / (15 / 16) := div_le_div_of_nonneg_left (by positivity)
          (by norm_num : (0 : ℝ) < 15 / 16) (by linarith only [hbudget.2])
        _ = _ := by ring
    intro t ht
    have HC := hcap (8000 * (Y a 1 + Y a 3) / μ) hfinal t ht
    exact ⟨hfinal t ht, HC.1.trans_eq (by dsimp [q]; ring), HC.2.trans_eq (by dsimp [q]; ring)⟩
  · have hq0 : 0 ≤ q z := by dsimp [q]; positivity
    have htime : 0 ≤ z - a := sub_nonneg.mpr hz.1
    have Hphase := connectionPhase_growing_variation_bound hμ hw0 (hm z hz) (hu z hz)
      ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz) (D z) (hζ z hz)
      (by positivity : 0 ≤ 32 * (1 + q z))
      (by positivity : 0 ≤ 12800 * Y a 1 + 64 * q z + 128 * (z - a) * Q)
      (hcap Q hQ z hz).1 (hcap Q hQ z hz).2
    have hJ : 0 ≤ 64 * (Y z 1 / μ ^ 2 + (Y z 2 * Y z 3) ^ 2 / μ ^ 4) := by
      have hU := (hu z hz).1
      positivity
    apply Hphase.trans ((add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (hQ z hz) hJ) (le_refl _)) (le_refl _)) (le_refl _)).trans_eq ?_)
    dsimp [e, k, q, connectionGrowingFeedbackSource, connectionPhaseFeedbackRate]
    ring
