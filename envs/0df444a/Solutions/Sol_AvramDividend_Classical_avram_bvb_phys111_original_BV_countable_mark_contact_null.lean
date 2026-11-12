-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys111_original_BV_countable_mark_contact_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:42:01.119753+00:00
-- url     : https://prove2.me/submissions/a90cffc4-df42-4917-a08b-86b9c4bd54c6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- Any countable collection of zero-reserve contact marks has zero
original Lévy mass under Standing and bounded variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (S : Set ℝ) (hS : S.Countable) : X.ν S = 0 := by
  letI : NullSingletonClass X.ν :=
    ⟨fun z =>
      avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
        X hStanding hBV z⟩
  exact hS.measure_zero X.ν
