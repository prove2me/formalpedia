-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_levy_negative_large_tail_at_half_reserve_buffer_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:13:02.260338+00:00
-- url     : https://prove2.me/submissions/cc2031f4-99a6-4042-acf0-73e423449b01

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Actual source negative Lévy mark intensity is finite below half the
strictly positive reserve localisation buffer, from the true quadratic energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : (∫⁻ z : ℝ,
      ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤)
    (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) :
    X.ν (Iic (-a / 2)) < ⊤ := by
  have hδpos : 0 < a / 2 := by linarith only [ha]
  have hδle : a / 2 ≤ (1 : ℝ) := by linarith only [ha2]
  simpa only [neg_div] using
    avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
      X.ν hν (a / 2) hδpos hδle
