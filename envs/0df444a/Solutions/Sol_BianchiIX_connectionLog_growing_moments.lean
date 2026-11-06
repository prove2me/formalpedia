-- Prove2me | solution 1 for BianchiIX.connectionLog_growing_moments
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T09:37:23.816754+00:00
-- url     : https://prove2.me/submissions/4a5c5de4-fa80-4552-aff4-5417dfeda366

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Theorems.Thm_BianchiIX_connectionLogField_components
import Theorems.Thm_BianchiIX_connectionLog_prefix_estimates
import Theorems.Thm_BianchiIX_connection_weak_clock_rates
import Theorems.Thm_BianchiIX_integral_le_of_dissipation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

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
open Set MeasureTheory

private theorem BianchiIX.integral_growing_square {W : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hW : ∀ t ∈ Icc a b, HasDerivAt W (W t) t) :
    (∫ t in a..b, W t ^ 2) = (W b ^ 2 - W a ^ 2) / 2 ∧
      (∫ t in a..b, W t ^ 2) ≤ W b ^ 2 / 2 := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun s => W s ^ 2 / 2) (W t ^ 2) t := by
    convert! ((hW t ht).pow 2).div_const 2 using 1
    ring
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (uIcc_of_le hab ▸ ht))
    (((HasDerivAt.continuousOn hW).pow 2).intervalIntegrable_of_Icc (μ := volume) hab)
  have hid : (∫ t in a..b, W t ^ 2) = (W b ^ 2 - W a ^ 2) / 2 := H.trans (by ring)
  exact ⟨hid, by rw [hid]; nlinarith only [sq_nonneg (W a)]⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.growing_wall_duration_bound {W : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hW : ∀ t ∈ Icc a b, HasDerivAt W (W t) t)
    (hW0 : ∀ t ∈ Icc a b, 0 ≤ W t) (hWb : W b ≤ 1) :
    W a * (b - a) ≤ 1 := by
  have hmono : MonotoneOn W (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (HasDerivAt.continuousOn hW)
      (fun t ht => (hW t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hW t (interior_subset ht)).deriv]
    exact hW0 t (interior_subset ht)
  have HI := intervalIntegral.integral_mono_on (μ := volume) hab (intervalIntegrable_const (c := W a))
    ((HasDerivAt.continuousOn hW).intervalIntegrable_of_Icc hab)
    (fun t ht => hmono ⟨le_rfl, hab⟩ ht ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hW t (uIcc_of_le hab ▸ ht))
      ((HasDerivAt.continuousOn hW).intervalIntegrable_of_Icc hab)] at HI
  nlinarith only [HI, hWb, hW0 a ⟨le_rfl, hab⟩]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_dissipative_growing_product {U U' W : ℝ → ℝ} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hU : ∀ t ∈ Icc a b, HasDerivAt U (U' t) t)
    (hdecay : ∀ t ∈ Icc a b, U' t ≤ -(μ / 2) * U t)
    (hU0 : ∀ t ∈ Icc a b, 0 ≤ U t)
    (hW : ∀ t ∈ Icc a b, HasDerivAt W (W t) t)
    (hW0 : ∀ t ∈ Icc a b, 0 ≤ W t) :
    (∫ t in a..b, U t * W t) ≤ 4 * U a * W a / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have H := integral_moments_le_of_linear_dissipation hab (by positivity : 0 < μ / 4)
    (fun t ht => (hU t ht).mul (hW t ht)) (fun t ht => ?_)
    (mul_nonneg (hU0 b ⟨hab, le_rfl⟩) (hW0 b ⟨hab, le_rfl⟩))
  · exact H.1.trans_eq (by simp only [Pi.mul_apply]; ring)
  · have Hd := mul_le_mul_of_nonneg_right (hdecay t ht) (hW0 t ht)
    have Hμ := mul_le_mul_of_nonneg_right hμ (mul_nonneg (hU0 t ht) (hW0 t ht))
    simp only [Pi.mul_apply]
    nlinarith only [Hd, Hμ]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_dissipative_growing_square {U U' W : ℝ → ℝ} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hU : ∀ t ∈ Icc a b, HasDerivAt U (U' t) t)
    (hdecay : ∀ t ∈ Icc a b, U' t ≤ -(μ / 2) * U t)
    (hU0 : ∀ t ∈ Icc a b, 0 ≤ U t)
    (hW : ∀ t ∈ Icc a b, HasDerivAt W (W t) t)
    (hW0 : ∀ t ∈ Icc a b, 0 ≤ W t) (hWb : W b ≤ 1) :
    (∫ t in a..b, U t * W t ^ 2) ≤ U a * W a := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) := (hU t ht).mul ((hW t ht).pow 2)
  have hanti : AntitoneOn (fun t => U t * W t ^ 2) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (HasDerivAt.continuousOn hd)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    have Hd := mul_le_mul_of_nonneg_right (hdecay t (interior_subset ht)) (sq_nonneg (W t))
    have Hμ := mul_le_mul_of_nonneg_right hμ (mul_nonneg (hU0 t (interior_subset ht)) (sq_nonneg (W t)))
    norm_num only [Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
    nlinarith only [Hd, Hμ]
  have HI := intervalIntegral.integral_mono_on (μ := volume) hab
    ((HasDerivAt.continuousOn hd).intervalIntegrable_of_Icc hab)
    (intervalIntegrable_const (c := U a * W a ^ 2)) (fun t ht => hanti ⟨le_rfl, hab⟩ ht ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at HI
  have Hlen := growing_wall_duration_bound hab hW hW0 hWb
  have Hprod := mul_le_mul_of_nonneg_left Hlen (mul_nonneg (hU0 a ⟨le_rfl, hab⟩) (hW0 a ⟨le_rfl, hab⟩))
  exact HI.trans (by nlinarith only [Hprod])

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

theorem solution {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    (∫ z in a..b, Y z 3 ^ 2) ≤ Y b 3 ^ 2 / 2 ∧
      (∫ z in a..b, Y z 1 * Y z 3) ≤ 4 * Y a 1 * Y a 3 / μ ∧
      (∫ z in a..b, Y z 1 * Y z 3 ^ 2) ≤ Y a 1 * Y a 3 ∧
      (∫ z in a..b, Y z 2 * Y z 3) ≤ μ * (Y a 2 * Y a 3) / 2 ∧
      (∫ z in a..b, (Y z 2 * Y z 3) ^ 2 * Y z 3 ^ 2) ≤ (Y a 2 * Y a 3) ^ 2 * Y b 3 ^ 2 / 2 := by
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
  have hW (z : ℝ) (hz : z ∈ Icc a b) : HasDerivAt (fun t => Y t 3) (Y z 3) z := by
    have H := hasDerivAt_pi.mp (hY z hz) 3
    rwa [(connectionLogField_components (ne_of_gt (hD z hz))).2.2.2] at H
  have Hsq := (integral_growing_square hab hW).2
  refine ⟨Hsq, integral_dissipative_growing_product hab hμ
    (fun z hz => hasDerivAt_pi.mp (hY z hz) 1) hU (fun z hz => (hu z hz).1) hW (fun z hz => (hw z hz).1),
    integral_dissipative_growing_square hab hμ
      (fun z hz => hasDerivAt_pi.mp (hY z hz) 1) hU (fun z hz => (hu z hz).1) hW
      (fun z hz => (hw z hz).1) (hw b ⟨hab, le_rfl⟩).2, ?_, ?_⟩
  · have HP := integral_moments_le_of_linear_dissipation hab (by positivity : 0 < 2 / μ)
      (fun z hz => hasDerivAt_connectionLog_product (hY z hz) (ne_of_gt (hD z hz)))
      (fun z hz => ?_) (mul_nonneg (hv b ⟨hab, le_rfl⟩).1.le (hw b ⟨hab, le_rfl⟩).1)
    · exact HP.1.trans_eq (by field_simp)
    · simpa only [neg_div, connectionClockRate, connectionSpeed] using mul_le_mul_of_nonneg_right
        (connection_weak_clock_rates hμ (hm z hz) (hu z hz) (hv' z hz) (hw z hz) (huv z hz)).2
        (mul_nonneg (hv z hz).1.le (hw z hz).1)
  · have hP (z : ℝ) (hz : z ∈ Icc a b) : Y z 2 * Y z 3 ≤ Y a 2 * Y a 3 := by
      have hsub : Icc a z ⊆ Icc a b := Icc_subset_Icc_right hz.2
      have H := (connectionLog_prefix_estimates hz.1 hμ (fun r hr => hY r (hsub hr))
        (fun r hr => hm r (hsub hr)) (fun r hr => hu r (hsub hr))
        (fun r hr => hv r (hsub hr)) (fun r hr => hw r (hsub hr)) hentry).2.2.2.1
      have he : Real.exp (-2 * (z - a) / μ) ≤ 1 := Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.mpr hz.1)) hμ0.le)
      exact H.trans ((mul_le_mul_of_nonneg_left he (mul_nonneg (hv a ⟨le_rfl, hab⟩).1.le
        (hw a ⟨le_rfl, hab⟩).1)).trans_eq (mul_one _))
    have hc := HasDerivAt.continuousOn hY
    have hcP : ContinuousOn (fun z => (Y z 2 * Y z 3) ^ 2) (Icc a b) :=
      ((continuousOn_pi.mp hc 2).mul (continuousOn_pi.mp hc 3)).pow 2
    have hcW : ContinuousOn (fun z => Y z 3 ^ 2) (Icc a b) := (continuousOn_pi.mp hc 3).pow 2
    have HI := intervalIntegral.integral_mono_on (μ := volume) hab
      ((hcP.mul hcW).intervalIntegrable_of_Icc hab) ((hcW.const_mul ((Y a 2 * Y a 3) ^ 2)).intervalIntegrable_of_Icc hab)
      (fun z hz => mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg (hv z hz).1.le (hw z hz).1) (hP z hz) 2) (sq_nonneg (Y z 3)))
    rw [intervalIntegral.integral_const_mul] at HI
    exact HI.trans ((mul_le_mul_of_nonneg_left Hsq (sq_nonneg (Y a 2 * Y a 3))).trans_eq (by ring))
