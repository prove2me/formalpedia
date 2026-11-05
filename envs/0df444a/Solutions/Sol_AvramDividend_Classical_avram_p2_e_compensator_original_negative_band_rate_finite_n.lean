-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_negative_band_rate_finite_n
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:27:30.561895+00:00
-- url     : https://prove2.me/submissions/6b88f0c8-306f-410b-9d88-0c601ad70cc7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The literal original negative-band Lévy rate for cutoff 1/(n+1) is finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    X.ν (Iic (-(1 / ((n : ℝ) + 1)))) < ⊤ := by
  let ε : ℝ := 1 / ((n : ℝ) + 1)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hν := avram_p2_a_zero_rate_separated_borel_nu_finite
    X (Iic (-ε)) measurableSet_Iic ε hε (Set.Subset.rfl)
  simpa only [ε] using hν
