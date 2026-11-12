-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18h_original_largejump_window_shift_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:52:16.641819+00:00
-- url     : https://prove2.me/submissions/c6a690fd-213d-4ada-ac4c-a1da8fba0962

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

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original large-negative mark window is a Borel functional of the
shifted original càdlàg path, using a measurable marked-jump extractor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ J : (ℝ≥0 → ℝ) → ℝ, Measurable J ∧
      ∀ ω : Ω,
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω -
          avram_p4_h_gaussian_intrinsic_large_jump_sum X s ω =
        J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
  classical
  let T : ℝ≥0 := t - s
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
  intro ω
  let Y : ℝ≥0 → ℝ := fun u => X.X (s + u) ω - X.X s ω
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
      (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u))
  have hNeg : ∀ z ∈ B, z ≤ 0 := by
    intro z hz
    exact hz.trans (by norm_num)
  have hT : s + T = t := add_tsub_cancel_of_le hst
  have hPath := avram_wave7_01_original_shifted_future_increment_path_cadlag X ω s
  have hWformula := hWpath Y hPath.1 hPath.2
  have hWindow := avram_ja18h_original_largejump_interval_difference
    X hX hFinite s t hst ω
  have hShift := avram_mix_fin14_original_negative_band_shift_integral_exact
    X ω s T B measurableSet_Iic hNeg
  have hSign := avram_mix_gauss14_generic_negative_mark_window_integral_formula
    μ (0 : ℝ≥0) T B measurableSet_Iic hNeg
  change _ = -((W Y).toReal)
  rw [hWindow, ← hT] at *
  calc
    (∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      (∫ p in (Ioc 0 T ×ˢ B), p.2 ∂μ) := by simpa [μ, Y] using hShift.symm
    _ = -((W Y).toReal) := by
      rw [hSign, hWformula]
