-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_same_source_weighted_cap_contact_clock_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:08:36.748077+00:00
-- url     : https://prove2.me/submissions/71dd2989-c86b-4161-8da6-58025aaa670d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
An arbitrary nonnegative generator or stochastic-characteristic density,
even infinite at cap contact, integrates to zero against each fixed s-finite
physical-time clock on the genuine original controlled UBV process.
-/

/-- No cap-boundary contribution from density terms on a deterministic time clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ]
    (weight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            riskProcess X x D t ω = c
        then weight t ω else 0 ∂μ) = 0 := by
  have hOcc :=
    avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
      X hBV x c D hD μ hCap
  filter_upwards [hOcc] with ω hω
  have hZero : ∀ᵐ (t : ℝ≥0) ∂μ,
      (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
          riskProcess X x D t ω = c
       then weight t ω else 0) = 0 := by
    filter_upwards [hω] with t ht
    by_cases hContact :
        0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
          riskProcess X x D t ω = c
    · have hLess := ht ⟨hContact.1, hContact.2.1⟩
      rw [hContact.2.2] at hLess
      exact False.elim ((lt_irrefl c) hLess)
    · simp [hContact]
  calc
    (∫⁻ t : ℝ≥0,
      if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
          riskProcess X x D t ω = c
      then weight t ω else 0 ∂μ) =
        ∫⁻ _t : ℝ≥0, (0 : ℝ≥0∞) ∂μ := lintegral_congr_ae hZero
    _ = 0 := by simp
