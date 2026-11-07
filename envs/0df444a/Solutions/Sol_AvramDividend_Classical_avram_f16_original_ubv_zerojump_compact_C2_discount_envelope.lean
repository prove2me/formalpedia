-- Prove2me | solution 1 for AvramDividend.Classical.avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:27:20.908221+00:00
-- url     : https://prove2.me/submissions/6e4da726-4b5d-49af-b060-c97c6b257eca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_ubv_zerojump_nonzero_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_positive_gaussian_compact_C2_discount_envelope
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
    (hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      (∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG) ∧
      (∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ KH) := by
  have hσne : X.σ ≠ 0 :=
    avram_p4_f4_original_ubv_zerojump_nonzero_gaussian X hBV hν
  have hσpos : 0 < X.σ :=
    lt_of_le_of_ne X.σ_nonneg (Ne.symm hσne)
  exact avram_f16_original_positive_gaussian_compact_C2_discount_envelope
    X hσpos q hq C w hw hopen a b hband
