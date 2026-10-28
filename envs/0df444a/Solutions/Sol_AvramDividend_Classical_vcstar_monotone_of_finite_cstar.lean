-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_monotone_of_finite_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:13:04.262994+00:00
-- url     : https://prove2.me/submissions/afd9da65-87cf-478c-967d-e372ee86b065

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_zero_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_positive_real_cstar
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The candidate value is globally monotone for every finite formal
optimal barrier, by the zero and strictly positive barrier cases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hcfin : cstar W < ⊤) :
    Monotone (vcstar W) := by
  by_cases hc0 : cstar W = 0
  · exact vcstar_monotone_of_zero_cstar X hX q hq W hW hc0
  · have hcnotop : cstar W ≠ ⊤ := ne_of_lt hcfin
    have hcpos : 0 < (cstar W).toReal := ENNReal.toReal_pos hc0 hcnotop
    exact vcstar_monotone_of_positive_real_cstar X q W hW hcpos
