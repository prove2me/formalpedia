-- Prove2me | solution 1 for AvramDividend.Classical.chat03_both_named_passage_clocks_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:18:37.963842+00:00
-- url     : https://prove2.me/submissions/493fb0e8-1c44-46bd-b8cc-519a3e30928b

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_ennreal_measurable_of_finite_strict_sublevels
import Theorems.Thm_AvramDividend_Classical_chat03_named_upper_passage_lt_horizon_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_named_lower_passage_lt_horizon_measurable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The named strict first-passage clocks are fully Borel measurable as
ENNReal-valued random times, including the value infinity.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) :
    Measurable (fun ω : Ω => twoSidedExitUpTime X upper ω) ∧
    Measurable (fun ω : Ω => twoSidedExitDownTime X lower ω) := by
  constructor
  · apply chat03_ennreal_measurable_of_finite_strict_sublevels
    exact chat03_named_upper_passage_lt_horizon_measurable X upper
  · apply chat03_ennreal_measurable_of_finite_strict_sublevels
    exact chat03_named_lower_passage_lt_horizon_measurable X lower
