-- Prove2me | solution 2 for CohnElkies.stripPoissonKernel_shifted_centered_interval_max
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:26:27.289992+00:00
-- url     : https://prove2.me/submissions/6dcb3435-3f64-46f3-a88c-e253ea1d2843

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology


theorem solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    (∫ x in Icc (-r) r,
      stripPoissonKernel σ (s - x)) ≤
      ∫ x in Icc (-r) r,
        stripPoissonKernel σ (0 - x) := by
  set P : ℝ → ℝ := stripPoissonKernel σ with hP
  have hθ0 : 0 < stripAngle σ := by unfold stripAngle; have := Real.pi_pos; nlinarith
  have hθπ : stripAngle σ < Real.pi := by unfold stripAngle; have := Real.pi_pos; nlinarith
  have hsin : 0 < Real.sin (stripAngle σ) := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hcos : Real.cos (stripAngle σ) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hθπ.le hθ0
    simpa using this
  have hden : ∀ x : ℝ, 0 < 4 * (Real.cosh (Real.pi * x / 2) - Real.cos (stripAngle σ)) := by
    intro x; have := Real.one_le_cosh (Real.pi * x / 2); linarith
  have hcont : Continuous P := by
    rw [hP]; unfold stripPoissonKernel
    exact continuous_const.div (by fun_prop) (fun x => (hden x).ne')
  have hII : ∀ a b : ℝ, IntervalIntegrable P volume a b := fun a b => hcont.intervalIntegrable a b
  have hmono : ∀ a b : ℝ, |b| ≤ |a| → P a ≤ P b := by
    intro a b hab
    rw [hP]; unfold stripPoissonKernel
    apply div_le_div_of_nonneg_left hsin.le (hden b)
    have : Real.cosh (Real.pi * b / 2) ≤ Real.cosh (Real.pi * a / 2) := by
      rw [Real.cosh_le_cosh]
      rw [show Real.pi * b / 2 = (Real.pi / 2) * b by ring, show Real.pi * a / 2 = (Real.pi / 2) * a by ring,
        abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left hab (abs_nonneg _)
    linarith
  have heven : ∀ x, P (-x) = P x := fun x => hmono _ _ (by rw [abs_neg]) |>.antisymm
    (hmono _ _ (by rw [abs_neg]))
  set G : ℝ → ℝ := fun t => ∫ y in t - r..t + r, P y with hG
  have hconv : ∀ t : ℝ, (∫ x in Icc (-r) r, P (t - x)) = G t := by
    intro t
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_sub_left (fun y => P y) t]
    simp only [hG]; congr 1 <;> ring
  have hpos : ∀ t : ℝ, 0 ≤ t → G t ≤ G 0 := by
    intro t ht
    simp only [hG]
    have e1 := intervalIntegral.integral_add_adjacent_intervals (hII (t - r) r) (hII r (t + r))
    have e2 := intervalIntegral.integral_add_adjacent_intervals (hII (0 - r) (t - r)) (hII (t - r) r)
    rw [show (0:ℝ) + r = r by ring]
    have h1 : (∫ y in r..t + r, P y) = ∫ x in (0:ℝ)..t, P (x + r) := by
      rw [intervalIntegral.integral_comp_add_right (fun y => P y) r]; simp
    have h2 : (∫ y in 0 - r..t - r, P y) = ∫ x in (0:ℝ)..t, P (x - r) := by
      rw [intervalIntegral.integral_comp_sub_right (fun y => P y) r]
    have h3 : (∫ x in (0:ℝ)..t, P (x + r)) ≤ ∫ x in (0:ℝ)..t, P (x - r) := by
      apply intervalIntegral.integral_mono_on ht
      · exact (hcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
      · exact (hcont.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
      · intro x hx
        apply hmono
        rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x + r), abs_le]
        constructor <;> linarith [hx.1]
    linarith [e1, e2, h1, h2, h3]
  have hGeven : ∀ t, G (-t) = G t := by
    intro t
    simp only [hG]
    calc (∫ y in -t - r..-t + r, P y) = ∫ y in -t - r..-t + r, P (-y) := by simp only [heven]
      _ = ∫ y in -(-t + r)..-(-t - r), P y := intervalIntegral.integral_comp_neg (fun y => P y)
      _ = _ := by congr 1 <;> ring
  rw [hconv s, hconv 0]
  rcases le_total 0 s with h | h
  · exact hpos s h
  · rw [← hGeven s]; exact hpos (-s) (by linarith)

