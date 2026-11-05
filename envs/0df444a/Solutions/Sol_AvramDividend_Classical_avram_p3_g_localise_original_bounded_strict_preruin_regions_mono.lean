-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_bounded_strict_preruin_regions_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:30:58.637201+00:00
-- url     : https://prove2.me/submissions/4675aace-bf79-49f0-b0df-ba8308e08118

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original finite-clock strict pre-ruin masks are nested
as the deterministic horizon grows. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ∀ T₁ T₂ : ℝ≥0, T₁ ≤ T₂ →
      ({p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) <
          (((min (ruinTime X x D p.2) (T₁ : ℝ≥0∞)).toNNReal) : ℝ≥0∞)} :
        Set (ℝ≥0 × Ω)) ⊆
      {p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) <
          (((min (ruinTime X x D p.2) (T₂ : ℝ≥0∞)).toNNReal) : ℝ≥0∞)} := by
  intro T₁ T₂ hT p hp
  have hPre :=
    ((avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
      X x D T₁).1 p.2 p.1).mp hp
  exact
    ((avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
      X x D T₂).1 p.2 p.1).mpr
      ⟨hPre.1, lt_of_lt_of_le hPre.2 hT⟩
