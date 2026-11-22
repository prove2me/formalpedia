-- Prove2me | solution 1 for Complex.gamma_ratio_fixed_shift_vertical_bound
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T20:17:03.082189+00:00
-- url     : https://prove2.me/submissions/9ae41b39-b126-4e24-809a-4c480fbd1147

import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_complex_stirling

set_option autoImplicit false

namespace GammaRatioAux
open Complex Real

/-- y·(π/2 - arg z) is bounded for re z > 0, im z > 0. -/
lemma gr_arg_bound (z : ℂ) (ha : 0 < z.re) (hy : 0 < z.im) :
    0 ≤ z.im * (π/2 - arg z) ∧ z.im * (π/2 - arg z) ≤ π/2 * z.re := by
  have hz : z ≠ 0 := fun h => by simp [h] at ha
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : arg z ≤ π/2 := arg_le_pi_div_two_iff.mpr (Or.inl ha.le)
  have h0 : 0 ≤ arg z := arg_nonneg_iff.mpr hy.le
  have hc := cos_arg hz
  have hs : Real.sin (π/2 - arg z) = z.re / ‖z‖ := by rw [Real.sin_pi_div_two_sub, hc]
  have hj := mul_le_sin (x := π/2 - arg z) (by linarith) (by linarith)
  rw [hs] at hj
  have him : z.im ≤ ‖z‖ := (le_abs_self _).trans (abs_im_le_norm z)
  refine ⟨mul_nonneg hy.le (by linarith), ?_⟩
  have hφ : π/2 - arg z ≤ π/2 * (z.re / ‖z‖) := by
    have := pi_pos; rw [div_mul_eq_mul_div, div_le_iff₀ pi_pos] at hj
    nlinarith
  calc z.im * (π/2 - arg z) ≤ z.im * (π/2 * (z.re / ‖z‖)) := mul_le_mul_of_nonneg_left hφ hy.le
    _ = π/2 * z.re * (z.im / ‖z‖) := by ring
    _ ≤ π/2 * z.re * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_one hn]; exact him
    _ = _ := by ring

/-- log-Stirling with explicit bound, positive real part, im ≥ 1. -/
lemma gr_log_stirling_pos (a : ℝ) (ha : 0 < a) :
    ∃ K, ∀ y : ℝ, 1 ≤ y →
      |Real.log ‖Gamma (a + y * I)‖ - ((a - 1/2) * Real.log y - π * y / 2)| ≤ K := by
  refine ⟨|a - 1/2| * a + π/2 * a + a + |Real.log (2*π)|/2 + 1/12 + 1, fun y hy => ?_⟩
  set z : ℂ := a + y * I with hzdef
  have hre : z.re = a := by simp [z]
  have him : z.im = y := by simp [z]
  obtain ⟨ρ, hρ, hΓ⟩ := TaoFivePrimes.rh_high_height_complex_stirling.1 z (by rw [hre]; exact ha)
    (by rw [him]; exact hy)
  have hz : z ≠ 0 := fun h => by have := congrArg Complex.re h; simp [z] at this; linarith
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hyz : y ≤ ‖z‖ := by rw [← him]; exact (le_abs_self _).trans (abs_im_le_norm z)
  have hzy : ‖z‖ ≤ a + y := by
    calc ‖z‖ ≤ ‖(a:ℂ)‖ + ‖(y:ℂ) * I‖ := norm_add_le _ _
      _ = a + y := by simp [abs_of_pos ha, abs_of_pos (by linarith : (0:ℝ) < y)]
  rw [hΓ, norm_exp, Real.log_exp]
  -- real part computation
  have hRe : ((z - 1/2) * Complex.log z - z + (Real.log (2*π):ℂ)/2 + 1/(12*z) + ρ).re
      = (a - 1/2) * Real.log ‖z‖ - y * arg z - a + Real.log (2*π)/2 + (1/(12*z)).re + ρ.re := by
    simp only [add_re, sub_re, mul_re, log_re, log_im, hre, him]
    simp [z]
  rw [hRe]
  have hlog1 : 0 ≤ Real.log ‖z‖ - Real.log y := by
    have := Real.log_le_log (by linarith) hyz; linarith
  have hlog2 : Real.log ‖z‖ - Real.log y ≤ a := by
    rw [← Real.log_div hn.ne' (by linarith)]
    calc Real.log (‖z‖ / y) ≤ ‖z‖ / y - 1 := Real.log_le_sub_one_of_pos (div_pos hn (by linarith))
      _ ≤ a := by
        rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]; nlinarith
  have harg := gr_arg_bound z (by rw [hre]; exact ha) (by rw [him]; linarith)
  rw [him, hre] at harg
  have h12 : |(1/(12*z)).re| ≤ 1/12 := by
    refine (abs_re_le_norm _).trans ?_
    rw [norm_div, norm_mul, norm_one]
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hn) (by norm_num)]
    simp; nlinarith
  have hρ' : |ρ.re| ≤ 1 := by
    refine (abs_re_le_norm _).trans (hρ.trans ?_)
    rw [him, div_le_one (by positivity)]; exact one_le_pow₀ hy
  have hA : |(a - 1/2) * (Real.log ‖z‖ - Real.log y)| ≤ |a - 1/2| * a := by
    rw [abs_mul, abs_of_nonneg hlog1]; exact mul_le_mul_of_nonneg_left hlog2 (abs_nonneg _)
  have hL : |Real.log (2*π)/2| ≤ |Real.log (2*π)|/2 := by rw [abs_div]; norm_num
  have key : (a - 1/2) * Real.log ‖z‖ - y * arg z - a + Real.log (2*π)/2 + (1/(12*z)).re + ρ.re
      - ((a - 1/2) * Real.log y - π * y / 2)
      = (a - 1/2) * (Real.log ‖z‖ - Real.log y) + y * (π/2 - arg z) - a + Real.log (2*π)/2
        + (1/(12*z)).re + ρ.re := by ring
  rw [key]
  have e1 := abs_le.mp hA; have e2 := abs_le.mp h12; have e3 := abs_le.mp hρ'; have e4 := abs_le.mp hL
  rw [abs_le]; constructor <;> nlinarith [harg.1, harg.2, abs_nonneg (a - 1/2), abs_nonneg (Real.log (2*π))]


lemma gr_Gamma_ne_zero_of_im (z : ℂ) (h : z.im ≠ 0) : Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm; apply h; rw [hm]; simp

/-- log-Stirling, any real part, im ≥ 1 -/
lemma gr_log_stirling_up (a : ℝ) :
    ∃ K, ∀ y : ℝ, 1 ≤ y →
      |Real.log ‖Gamma (a + y * I)‖ - ((a - 1/2) * Real.log y - π * y / 2)| ≤ K := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-a)
  suffices H : ∀ n : ℕ, ∀ a : ℝ, 0 < a + n → ∃ K, ∀ y : ℝ, 1 ≤ y →
      |Real.log ‖Gamma (a + y * I)‖ - ((a - 1/2) * Real.log y - π * y / 2)| ≤ K from
    H n a (by linarith)
  intro n
  induction n with
  | zero => intro a ha; exact gr_log_stirling_pos a (by simpa using ha)
  | succ n ih =>
    intro a ha
    obtain ⟨K, hK⟩ := ih (a + 1) (by push_cast at ha ⊢; linarith)
    refine ⟨K + |a| + 1, fun y hy => ?_⟩
    have h := hK y hy
    set z : ℂ := a + y * I
    have hzim : z.im = y := by simp [z]
    have hz : z ≠ 0 := fun h0 => by have := congrArg Complex.im h0; simp [z] at this; linarith
    have hz1 : ((a + 1 : ℝ) : ℂ) + y * I = z + 1 := by simp [z]; ring
    rw [hz1, Complex.Gamma_add_one z hz, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hz)
        (norm_ne_zero_iff.mpr (gr_Gamma_ne_zero_of_im z (by rw [hzim]; linarith)))] at h
    have hn0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hyz : y ≤ ‖z‖ := by rw [← hzim]; exact (le_abs_self _).trans (abs_im_le_norm z)
    have hzy : ‖z‖ ≤ |a| + y := by
      calc ‖z‖ ≤ ‖(a:ℂ)‖ + ‖(y:ℂ) * I‖ := norm_add_le _ _
        _ = |a| + y := by simp [abs_of_pos (by linarith : (0:ℝ) < y)]
    have hlog1 : 0 ≤ Real.log ‖z‖ - Real.log y := by
      have := Real.log_le_log (by linarith) hyz; linarith
    have hlog2 : Real.log ‖z‖ - Real.log y ≤ |a| := by
      rw [← Real.log_div hn0.ne' (by linarith)]
      calc Real.log (‖z‖ / y) ≤ ‖z‖ / y - 1 := Real.log_le_sub_one_of_pos (div_pos hn0 (by linarith))
        _ ≤ |a| := by
          rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]; nlinarith [abs_nonneg a]
    have hly : 0 ≤ Real.log y := Real.log_nonneg hy
    have := abs_le.mp h
    rw [abs_le]; constructor <;> nlinarith

/-- log-Stirling, any real part, |im| ≥ 1 -/
lemma gr_log_stirling (a : ℝ) :
    ∃ K, ∀ y : ℝ, 1 ≤ |y| →
      |Real.log ‖Gamma (a + y * I)‖ - ((a - 1/2) * Real.log |y| - π * |y| / 2)| ≤ K := by
  obtain ⟨K, hK⟩ := gr_log_stirling_up a
  refine ⟨K, fun y hy => ?_⟩
  rcases le_or_gt 0 y with h0 | h0
  · rw [abs_of_nonneg h0] at hy ⊢; exact hK y hy
  · rw [abs_of_neg h0] at hy ⊢
    have hc : (a : ℂ) + y * I = (starRingEnd ℂ) ((a:ℂ) + ((-y : ℝ):ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hc, Complex.Gamma_conj, Complex.norm_conj]
    exact hK (-y) hy


lemma gr_log_close (s Y : ℝ) (hs : 0 < s) (h1 : s/2 ≤ Y) (h2 : Y ≤ 2*s) :
    |Real.log Y - Real.log s| ≤ Real.log 2 := by
  have hY : 0 < Y := by linarith
  rw [abs_le]; constructor
  · have := Real.log_le_log (by positivity) h1
    rw [Real.log_div hs.ne' (by norm_num)] at this; linarith
  · have := Real.log_le_log hY h2
    rw [Real.log_mul (by norm_num) hs.ne'] at this; linarith

end GammaRatioAux

open Complex Real GammaRatioAux in
theorem solution
    (a b u v k : ℝ) (hk : 0 < k) :
    ∃ C T : ℝ, 0 ≤ C ∧ 1 ≤ T ∧
      ∀ (t : ℝ) (z w : ℂ), T ≤ |t| →
        z.re = a → w.re = b → z.im = u - k * t → w.im = v + k * t →
        ‖Complex.Gamma z / Complex.Gamma w‖ ≤ C * |t| ^ (a - b) := by
  obtain ⟨K1, hK1⟩ := gr_log_stirling a
  obtain ⟨K2, hK2⟩ := gr_log_stirling b
  set M := K1 + K2 + |a - 1/2| * Real.log 2 + |b - 1/2| * Real.log 2 + π/2 * (|u| + |v|) with hM
  refine ⟨Real.exp (M + (a - b) * Real.log k), max 1 ((2*|u| + 2*|v| + 2)/k),
    (Real.exp_pos _).le, le_max_left _ _, ?_⟩
  intro t z w hT hza hwb hzi hwi
  have ht1 : 1 ≤ |t| := (le_max_left _ _).trans hT
  have ht0 : 0 < |t| := by linarith
  have hsT : 2*|u| + 2*|v| + 2 ≤ k * |t| := by
    have := (le_max_right _ _).trans hT
    rw [div_le_iff₀ hk] at this; have := mul_comm k |t|; linarith
  set s := k * |t| with hsdef
  have hs : 0 < s := mul_pos hk ht0
  have hu0 := abs_nonneg u; have hv0 := abs_nonneg v
  -- |u - kt| and |v + kt| are within |u|, |v| of s
  have hkt : |k * t| = s := by rw [abs_mul, abs_of_pos hk]
  have hY1a : s - |u| ≤ |u - k*t| := by
    have := abs_sub_abs_le_abs_sub (k*t) u; rw [abs_sub_comm (k*t)] at this; linarith
  have hY1b : |u - k*t| ≤ s + |u| := by have := abs_sub u (k*t); linarith
  have hY2a : s - |v| ≤ |v + k*t| := by
    have := abs_sub_abs_le_abs_sub (k*t) (-v); simp only [sub_neg_eq_add, abs_neg] at this
    rw [add_comm] at this; linarith
  have hY2b : |v + k*t| ≤ s + |v| := by have := abs_add_le v (k*t); linarith
  have hz : z = (a:ℂ) + ((u - k*t : ℝ):ℂ) * I := by apply Complex.ext <;> simp [hza, hzi]
  have hw : w = (b:ℂ) + ((v + k*t : ℝ):ℂ) * I := by apply Complex.ext <;> simp [hwb, hwi]
  have e1 := abs_le.mp (hK1 (u - k*t) (by linarith))
  have e2 := abs_le.mp (hK2 (v + k*t) (by linarith))
  rw [← hz] at e1; rw [← hw] at e2
  have l1 := abs_le.mp (gr_log_close s |u - k*t| hs (by linarith) (by linarith))
  have l2 := abs_le.mp (gr_log_close s |v + k*t| hs (by linarith) (by linarith))
  have m1 : |(a - 1/2) * (Real.log |u - k*t| - Real.log s)| ≤ |a - 1/2| * Real.log 2 := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left
      (gr_log_close s _ hs (by linarith) (by linarith)) (abs_nonneg _)
  have m2 : |(b - 1/2) * (Real.log |v + k*t| - Real.log s)| ≤ |b - 1/2| * Real.log 2 := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left
      (gr_log_close s _ hs (by linarith) (by linarith)) (abs_nonneg _)
  have m1' := abs_le.mp m1; have m2' := abs_le.mp m2
  have hzim : z.im ≠ 0 := by rw [hzi]; intro h0; rw [h0, abs_zero] at hY1a; linarith
  have hwim : w.im ≠ 0 := by rw [hwi]; intro h0; rw [h0, abs_zero] at hY2a; linarith
  have hGz := norm_pos_iff.mpr (gr_Gamma_ne_zero_of_im z hzim)
  have hGw := norm_pos_iff.mpr (gr_Gamma_ne_zero_of_im w hwim)
  have hlogs : Real.log s = Real.log k + Real.log |t| := Real.log_mul hk.ne' ht0.ne'
  have key : Real.log ‖Gamma z / Gamma w‖ ≤ M + (a - b) * Real.log k + (a - b) * Real.log |t| := by
    rw [norm_div, Real.log_div hGz.ne' hGw.ne']
    have : (a - b) * Real.log k + (a - b) * Real.log |t| = (a - 1/2) * Real.log s - (b - 1/2) * Real.log s := by
      rw [hlogs]; ring
    rw [add_assoc, this, hM]
    rw [mul_sub] at m1' m2'
    have hp : π*|v + k*t|/2 - π*|u - k*t|/2 ≤ π/2*(|u|+|v|) := by nlinarith [pi_pos]
    linarith [m1'.2, m2'.1, e1.2, e2.1]
  calc ‖Gamma z / Gamma w‖ = Real.exp (Real.log ‖Gamma z / Gamma w‖) :=
        (Real.exp_log (by rw [norm_div]; exact div_pos hGz hGw)).symm
    _ ≤ Real.exp (M + (a - b) * Real.log k + (a - b) * Real.log |t|) := Real.exp_le_exp.mpr key
    _ = Real.exp (M + (a - b) * Real.log k) * |t| ^ (a - b) := by
        rw [Real.exp_add, Real.rpow_def_of_pos ht0, mul_comm (Real.log |t|)]
