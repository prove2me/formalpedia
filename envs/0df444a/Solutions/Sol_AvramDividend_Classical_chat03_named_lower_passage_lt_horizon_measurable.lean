-- Prove2me | solution 1 for AvramDividend.Classical.chat03_named_lower_passage_lt_horizon_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:47:35.20899+00:00
-- url     : https://prove2.me/submissions/006cc0cd-f167-42ba-a311-42425fa2b63a

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_generic_extended_infimum_lt_horizon
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_measurable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Strict sublevel events of the official named lower passage clock
are measurable at every deterministic finite NNReal horizon.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower : ℝ) (T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | twoSidedExitDownTime X lower ω < (T : ℝ≥0∞)} := by
  have hEq :
      {ω : Ω | twoSidedExitDownTime X lower ω < (T : ℝ≥0∞)} =
      {ω : Ω | ∃ s : ℝ≥0, s < T ∧ X.X s ω < lower} := by
    ext ω
    change
      (⨅ (s : ℝ≥0) (_ : X.X s ω < lower), (s : ℝ≥0∞)) <
        (T : ℝ≥0∞) ↔
        ∃ s : ℝ≥0, s < T ∧ X.X s ω < lower
    simpa only [and_comm] using
      (chat03_generic_extended_infimum_lt_horizon
        (fun s : ℝ≥0 => X.X s ω < lower) T)
  rw [hEq]
  exact chat03_lower_before_horizon_measurable X lower T

