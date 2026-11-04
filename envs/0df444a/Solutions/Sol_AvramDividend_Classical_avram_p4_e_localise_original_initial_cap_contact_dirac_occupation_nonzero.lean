-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_initial_cap_contact_dirac_occupation_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:34:27.320466+00:00
-- url     : https://prove2.me/submissions/29303e84-33fc-4af1-9662-eb5cab40bac2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The initial cap boundary can carry positive mass for a time measure charging zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0∞) (ω : Ω)
    (hτ0 : 0 < τ ω)
    (hCap0 : riskProcess X x D 0 ω = c) :
    (∫⁻ t : ℝ≥0,
      if (t : ℝ≥0∞) < τ ω ∧ riskProcess X x D t ω = c
      then (1 : ℝ≥0∞) else 0 ∂(Measure.dirac (0 : ℝ≥0))) = 1 := by
  simp [hτ0, hCap0]
