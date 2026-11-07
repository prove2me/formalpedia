-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_finitecap_real_interior_HJB_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:17:41.21019+00:00
-- url     : https://prove2.me/submissions/4970affa-2df1-497c-95b5-65ab3328d952

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact capped original HJB domain is a finite real open interval.
    The conversion does not assert smoothness at either boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ContDiffOn ℝ 2 w (Ioo 0 C.toReal) ∧
    (∀ y : ℝ, 0 < y → y < C.toReal →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → y < C.toReal → 1 ≤ deriv w y) := by
  have hInterior : Ioo (0 : ℝ) C.toReal =
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    ext y
    simp only [mem_Ioo, mem_setOf_eq]
    constructor
    · rintro ⟨hy, hyC⟩
      exact ⟨hy, (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy) hFinite).2 hyC⟩
    · rintro ⟨hy, hyC⟩
      exact ⟨hy, (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy) hFinite).1 hyC⟩
  constructor
  · simpa only [hInterior] using hw_smooth
  constructor
  · intro y hy hyC
    exact hw_gen y hy
      ((ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy) hFinite).2 hyC)
  · intro y hy hyC
    exact hw_grad y hy
      ((ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy) hFinite).2 hyC)
