-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_finite_attained_times_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:32:32.950055+00:00
-- url     : https://prove2.me/submissions/6abd58de-6fb9-4206-b457-58728f8a8081

import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-- Finite representatives of the original ordered extended-real first
strict upcrossing infima inherit their ordering as real times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b c : ℝ) (hbc : b ≤ c)
    (u v : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : c < X.X r ω), (r : ℝ≥0∞))) : (u : ℝ) ≤ (v : ℝ) := by
  have he : (u : ℝ≥0∞) ≤ (v : ℝ≥0∞) := by
    rw [hu, hv]
    exact firstUpcrossing_threshold_iInf_mono X ω b c hbc
  exact_mod_cast he
