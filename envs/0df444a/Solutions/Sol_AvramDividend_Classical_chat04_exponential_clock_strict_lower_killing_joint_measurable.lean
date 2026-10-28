-- Prove2me | solution 1 for AvramDividend.Classical.chat04_exponential_clock_strict_lower_killing_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T12:53:24.784356+00:00
-- url     : https://prove2.me/submissions/55d910c0-f5f6-408d-89b5-b44b81efecea

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The true strict lower-killed exponential-time observation event is
    jointly measurable in the Lévy path and real observation time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ) :
    MeasurableSet
      {z : Ω × ℝ | 0 ≤ z.2 ∧
        ENNReal.ofReal z.2 < twoSidedExitDownTime X lower z.1} := by
  have hclock : Measurable
      (fun ω : Ω => twoSidedExitDownTime X lower ω) :=
    (chat03_both_named_passage_clocks_measurable X lower 0).2
  have hright : Measurable
      (fun z : Ω × ℝ => twoSidedExitDownTime X lower z.1) :=
    hclock.comp measurable_fst
  have hleft : Measurable
      (fun z : Ω × ℝ => ENNReal.ofReal z.2) :=
    ENNReal.measurable_ofReal.comp measurable_snd
  have hn : MeasurableSet {z : Ω × ℝ | 0 ≤ z.2} :=
    measurableSet_le measurable_const measurable_snd
  have ht : MeasurableSet
      {z : Ω × ℝ |
        ENNReal.ofReal z.2 < twoSidedExitDownTime X lower z.1} :=
    measurableSet_lt hleft hright
  exact hn.inter ht
