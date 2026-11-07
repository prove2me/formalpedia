-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_topcap_positive_halfline_HJB_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:23:24.417131+00:00
-- url     : https://prove2.me/submissions/d0844079-a4c1-4612-8c8c-14a55fe71305

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original unbounded cap admits every strictly positive real reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ContDiffOn ℝ 2 w (Ioi 0) ∧
    (∀ y : ℝ, 0 < y → X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → 1 ≤ deriv w y) := by
  have hInterior : Ioi (0 : ℝ) =
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    ext y
    simp [hTop]
  constructor
  · simpa only [hInterior] using hw_smooth
  constructor
  · intro y hy
    exact hw_gen y hy (by simp [hTop])
  · intro y hy
    exact hw_grad y hy (by simp [hTop])
