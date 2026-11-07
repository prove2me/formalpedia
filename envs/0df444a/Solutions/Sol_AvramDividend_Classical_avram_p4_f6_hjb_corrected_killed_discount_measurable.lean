-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_hjb_corrected_killed_discount_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:35:03.249167+00:00
-- url     : https://prove2.me/submissions/9a38efb0-d8c5-42d0-b054-c8a55bbdbbdf

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q lower upper : ℝ) :
    Measurable (fun ω : Ω => twoSidedExitUpTimeCorrected X upper ω) ∧
    Measurable (fun ω : Ω => twoSidedExitDownTimeCorrected X lower ω) ∧
    Measurable (fun ω : Ω => ENNReal.ofReal (Real.exp
      (-(q * (twoSidedExitUpTimeCorrected X upper ω).toReal)))) := by
  have hclocks := chat03_both_named_passage_clocks_measurable X lower upper
  have hu : Measurable (fun ω : Ω => twoSidedExitUpTimeCorrected X upper ω) := by
    change Measurable (fun ω : Ω => twoSidedExitUpTime X upper ω)
    exact hclocks.1
  have hd : Measurable (fun ω : Ω => twoSidedExitDownTimeCorrected X lower ω) := by
    change Measurable (fun ω : Ω => twoSidedExitDownTime X lower ω)
    exact hclocks.2
  refine ⟨hu, hd, ?_⟩
  exact (Real.measurable_exp.comp ((measurable_const.mul hu.ennreal_toReal).neg)).ennreal_ofReal
