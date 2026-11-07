-- Prove2me | solution 1 for AvramDividend.Classical.avram_f16_original_ubv_zerojump_compact_C2_autoopen_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:35:38.441265+00:00
-- url     : https://prove2.me/submissions/bd8af7c9-ffd7-455b-a024-e24baee44aa6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      (∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG) ∧
      (∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ KH)  := by
  exact avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
    X hBV hν q hq C w hw
    (avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen C)
    a b hband
