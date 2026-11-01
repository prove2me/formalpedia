-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_sigma_finite_l2_band_cutoff_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:22:30.703328+00:00
-- url     : https://prove2.me/submissions/b93c5f98-160e-422c-adf8-06d44693fcd4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_levy_square_energy_band_tails

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (hf : Measurable f)
    (henergy : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ∞)
    (B : ℕ → Set α)
    (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, μ (B n) < ∞)
    (hBmono : Monotone B)
    (hBcover : (⋃ n, B n) = Set.univ) :
    Tendsto (fun n : ℕ =>
      eLpNorm ((B n)ᶜ.indicator f) (2 : ℝ≥0∞) μ)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hg : Measurable (fun x : α => ‖f x‖ₑ ^ (2 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable.comp hf.enorm
  have htail :=
    AvramDividend.Classical.avram_wave4_p1_levy_square_energy_band_tails
      μ (fun x : α => ‖f x‖ₑ ^ (2 : ℝ))
      hg henergy B hB hBfinite hBmono hBcover
  have hnorm (n : ℕ) :
      eLpNorm ((B n)ᶜ.indicator f) (2 : ℝ≥0∞) μ =
        (∫⁻ x in (B n)ᶜ, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hB n).compl]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  have hpow := Filter.Tendsto.ennrpow_const (1 / (2 : ℝ)) htail
  have hzero : (0 : ℝ≥0∞) ^ (1 / (2 : ℝ)) = 0 := by norm_num
  rw [hzero] at hpow
  simpa only [hnorm] using hpow
