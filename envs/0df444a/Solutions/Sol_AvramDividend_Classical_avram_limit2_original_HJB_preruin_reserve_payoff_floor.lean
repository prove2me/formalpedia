-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_HJB_preruin_reserve_payoff_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:44:20.659137+00:00
-- url     : https://prove2.me/submissions/b4d7d750-89bf-4d72-aa91-f7e5b989d3f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_HJB_all_variation_payoff_above_reserve
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The physical pre-ruin reserve never exceeds its original HJB payoff,
    uniformly in the BV and UBV branches and including cap contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwBV : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwUBV : ¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwHJB : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    ∀ (x : ℝ), 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ ω (t : ℝ≥0),
        (t : ℝ≥0∞) < ruinTime X x D ω →
        riskProcess X x D t ω ≤ w (riskProcess X x D t ω) := by
  intro x hx hxc D hD ω t ht
  obtain ⟨hNonneg, hBound⟩ :=
    capped_riskProcess_range_before_ruin_including_zero
      X x hx C hxc D hD ω t ht
  exact avram_limit2_original_HJB_all_variation_payoff_above_reserve
    X q w C hC hw0 hwCont hwBV hwUBV hwHJB _ hNonneg hBound
