-- Prove2me | solution 1 for AvramDividend.Classical.chat03_named_upper_passage_lt_horizon_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:39:36.213559+00:00
-- url     : https://prove2.me/submissions/8f2539a4-0111-49ff-9e54-b3ff725f256b

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_lt_iff_exists_witness
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_horizon_measurable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Strict sublevel sets for the official named upper passage clock are
measurable at every finite nonnegative horizon.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (upper : ℝ) (T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | twoSidedExitUpTime X upper ω < (T : ℝ≥0∞)} := by
  have hEq :
      {ω : Ω | twoSidedExitUpTime X upper ω < (T : ℝ≥0∞)} =
      {ω : Ω | ∃ s : ℝ≥0, s < T ∧ upper < X.X s ω} := by
    ext ω
    change
      (⨅ (s : ℝ≥0) (_ : upper < X.X s ω), (s : ℝ≥0∞)) <
        (T : ℝ≥0∞) ↔
        ∃ s : ℝ≥0, s < T ∧ upper < X.X s ω
    simpa only [and_comm] using
      (firstUpcrossing_lt_iff_exists_witness X upper ω T)
  rw [hEq]
  exact chat03_upper_before_horizon_measurable X upper T

