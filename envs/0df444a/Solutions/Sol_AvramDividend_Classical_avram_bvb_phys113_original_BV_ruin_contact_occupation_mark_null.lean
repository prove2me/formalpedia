-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys113_original_BV_ruin_contact_occupation_mark_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:51:47.742003+00:00
-- url     : https://prove2.me/submissions/85215e39-332b-4eb8-918c-f3455535de4c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys111_original_BV_countable_mark_contact_null
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- The mark levels cancelling a measurable physical reserve path
on a positive-measure time set form a Lévy-null set under Standing-BV. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (μ : Measure ℝ≥0) [SFinite μ]
    (U : ℝ≥0 → ℝ) (hU : Measurable U) :
    X.ν {z : ℝ | 0 < μ {t : ℝ≥0 | U t = -z}} = 0 := by
  have hcount :
      ({z : ℝ | 0 < μ {t : ℝ≥0 | -U t = z}} : Set ℝ).Countable :=
    Measure.countable_meas_level_set_pos hU.neg
  have hnull := avram_bvb_phys111_original_BV_countable_mark_contact_null
    X hStanding hBV _ hcount
  simpa only [neg_eq_iff_eq_neg] using hnull
