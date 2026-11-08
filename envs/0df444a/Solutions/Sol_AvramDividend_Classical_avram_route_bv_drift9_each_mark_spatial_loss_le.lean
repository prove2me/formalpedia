-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_bv_drift9_each_mark_spatial_loss_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:02:06.076734+00:00
-- url     : https://prove2.me/submissions/6fb6ea05-4420-4031-9253-4507d7abe225

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hwzero : w 0 = 0) (ε : ℝ) (hε : 0 < ε)
    (hεC : ENNReal.ofReal ε < C) (z : ℝ) (hz : z < 0) :
    (∫ y in Ioc (0 : ℝ) ε, w y - w (y + z) ∂(volume : Measure ℝ)) ≤
      min ε (-z) * w ε := by
  have hmon : MonotoneOn w (Icc (0 : ℝ) ε) := by
    intro a ha b hb hab
    have hbc : ENNReal.ofReal b ≤ C := (ENNReal.ofReal_mono hb.2).trans hεC.le
    have hsec := avram_wave3_03_bv_full_cap_gradient_secant C hC w hw_cont
      hw_smooth hw_grad a b ha.1 hab hbc
    linarith
  have hzero (t : ℝ) (ht : t ≤ 0) : w t = 0 := by
    rcases lt_or_eq_of_le ht with hlt | heq
    · exact hw_neg t hlt
    · subst t; exact hwzero
  have hneg_cont : ContinuousOn w (Iic (0 : ℝ)) := by
    apply (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Iic 0)).congr
    intro t ht; exact hzero t ht
  have hall : Continuous w := by
    have hu := hneg_cont.union_of_isClosed hw_cont isClosed_Iic isClosed_Ici
    simpa only [Set.Iic_union_Ici, continuousOn_univ] using hu
  have hint_all (a b : ℝ) : IntervalIntegrable w volume a b := (hall.continuousOn : ContinuousOn w (uIcc a b)).intervalIntegrable
  have hshift_int : IntervalIntegrable (fun y => w (y + z)) volume 0 ε :=
    ((hall.comp (continuous_id.add continuous_const)).continuousOn : ContinuousOn
      (fun y : ℝ => w (y + z)) (uIcc 0 ε)).intervalIntegrable
  have hzero_interval (a b : ℝ) (hab : a ≤ b) (hb : b ≤ 0) :
      (∫ y in a..b, w y) = 0 := by
    calc
      _ = ∫ y in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact hzero y ((show y ∈ Icc a b by simpa [uIcc_of_le hab] using hy).2.trans hb)
      _ = 0 := by simp
  have hupper (a : ℝ) (ha0 : 0 ≤ a) (haε : a ≤ ε) :
      (∫ y in a..ε, w y) ≤ (ε - a) * w ε := by
    have hbound : ∀ y ∈ Icc a ε, w y ≤ w ε := by
      intro y hy; exact hmon ⟨ha0.trans hy.1, hy.2⟩ ⟨hε.le, le_refl _⟩ hy.2
    simpa using (intervalIntegral.integral_mono_on haε (hint_all a ε)
      intervalIntegrable_const hbound)
  have hshift :
      (∫ y in Ioc (0 : ℝ) ε, w y - w (y + z) ∂(volume : Measure ℝ)) =
        (∫ y in 0..ε, w y) - (∫ y in z..(ε + z), w y) := by
    calc
      _ = ∫ y in 0..ε, w y - w (y + z) := by rw [intervalIntegral.integral_of_le hε.le]
      _ = (∫ y in 0..ε, w y) - (∫ y in 0..ε, w (y + z)) :=
        intervalIntegral.integral_sub (hint_all 0 ε) hshift_int
      _ = (∫ y in 0..ε, w y) - (∫ y in z..(ε + z), w y) := by
        rw [intervalIntegral.integral_comp_add_right]; simp only [zero_add]
  by_cases hlarge : ε ≤ -z
  · have hlast : ε + z ≤ 0 := by linarith
    have hzero_shift : (∫ y in z..(ε + z), w y) = 0 := hzero_interval z (ε + z) (by linarith) hlast
    calc
      _ = (∫ y in 0..ε, w y) := by rw [hshift, hzero_shift]; ring
      _ ≤ ε * w ε := by simpa using (hupper 0 (le_refl _) hε.le)
      _ = min ε (-z) * w ε := by rw [min_eq_left hlarge]
  · have hmid : 0 ≤ ε + z ∧ ε + z ≤ ε := by constructor <;> linarith
    have hzero_shift : (∫ y in z..(0 : ℝ), w y) = 0 := hzero_interval z 0 hz.le (le_refl _)
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals (hint_all z 0) (hint_all 0 (ε + z))
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hint_all 0 (ε + z)) (hint_all (ε + z) ε)
    have hidentity :
        (∫ y in Ioc (0 : ℝ) ε, w y - w (y + z) ∂(volume : Measure ℝ)) =
          (∫ y in (ε + z)..ε, w y) := by
      rw [hshift]; linarith
    calc
      _ = (∫ y in (ε + z)..ε, w y) := hidentity
      _ ≤ (ε - (ε + z)) * w ε := hupper (ε + z) hmid.1 hmid.2
      _ = min ε (-z) * w ε := by
        have hshort : -z ≤ ε := by linarith
        rw [min_eq_right hshort]; ring
