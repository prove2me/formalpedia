-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_canonical_finite_negative_band_intensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:27:12.422955+00:00
-- url     : https://prove2.me/submissions/854b2ce6-a13d-4524-b00b-7ae7685cb036

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every canonical finite negative jump band bounded away from zero has
finite original Lévy intensity; no claim concerns the limiting infinite band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ n : ℕ,
      X.ν (Ioc (-1 : ℝ) (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ))) < ⊤ := by
  intro n
  have hpos : 0 < (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
  have hfin :=
    levy_negative_mass_away_from_zero_finite X
      ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) hpos
  have hsub :
      Ioc (-1 : ℝ) (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) ⊆
        Iic (-((1 : ℝ) / ((n + 1 : ℕ) : ℝ))) := by
    intro z hz
    change z ≤ -((1 : ℝ) / ((n + 1 : ℕ) : ℝ))
    simpa only [neg_div] using hz.2
  exact lt_of_le_of_lt (measure_mono hsub) hfin
