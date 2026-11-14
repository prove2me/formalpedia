-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_uniform_largejump_future_borel_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:35:19.570204+00:00
-- url     : https://prove2.me/submissions/409ac378-cb79-4eb1-a898-64c0bd1cba26

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_largejump_interval_difference
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_negative_band_shift_integral_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single Borel statistic represents the physical large-jump increment at all start times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    ∃ J : (ℝ≥0 → ℝ) → ℝ, Measurable J ∧
      ∀ (s : ℝ≥0) (ω : Ω),
        avram_p4_h_gaussian_intrinsic_large_jump_sum X (s + T) ω -
          avram_p4_h_gaussian_intrinsic_large_jump_sum X s ω =
        J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
  classical
  let B : Set ℝ := Iic (-1 : ℝ)
  let g : ℝ → ℝ≥0∞ := fun z =>
    if z ∈ B then ENNReal.ofReal (-z) else 0
  have hg : Measurable g := by
    dsimp [g]
    exact Measurable.ite measurableSet_Iic (by fun_prop) measurable_const
  obtain ⟨W, hW, hWpath⟩ :=
    avram_bv_jump8_cadlag_mark_weight_lintegral_borel T g hg
  let J : (ℝ≥0 → ℝ) → ℝ := fun Y => -((W Y).toReal)
  refine ⟨J, (ENNReal.measurable_toReal.comp hW).neg, ?_⟩
  intro s ω
  let Y : ℝ≥0 → ℝ := fun u => X.X (s + u) ω - X.X s ω
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
      (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u))
  have hNeg : ∀ z ∈ B, z ≤ 0 := by
    intro z hz
    exact hz.trans (by norm_num)
  have hPath :=
    avram_wave7_01_original_shifted_future_increment_path_cadlag X ω s
  have hWformula := hWpath Y hPath.1 hPath.2
  have hWindow := avram_ja18h_original_largejump_interval_difference
    X hX hFinite s (s + T) (le_add_of_nonneg_right zero_le) ω
  have hShift := avram_mix_fin14_original_negative_band_shift_integral_exact
    X ω s T B measurableSet_Iic hNeg
  have hSign := avram_mix_gauss14_generic_negative_mark_window_integral_formula
    μ (0 : ℝ≥0) T B measurableSet_Iic hNeg
  change _ = -((W Y).toReal)
  rw [hWindow]
  calc
    (∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      (∫ p in (Ioc 0 T ×ˢ B), p.2 ∂μ) := by
        simpa [μ, Y] using hShift.symm
    _ = -((W Y).toReal) := by
      rw [hSign, hWformula]
