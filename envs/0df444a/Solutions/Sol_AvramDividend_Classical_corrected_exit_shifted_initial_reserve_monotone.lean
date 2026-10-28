-- Prove2me | solution 1 for AvramDividend.Classical.corrected_exit_shifted_initial_reserve_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T08:03:21.108034+00:00
-- url     : https://prove2.me/submissions/7f3b8a2d-efb5-4812-bcf7-ef71fb8be0c9

import Theorems.Thm_AvramDividend_Classical_chat04_corrected_strict_exit_monotone_initial_reserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q h x y : ℝ) (hxy : x ≤ y) :
    twoSidedExitExpectationCorrected X q (h + x) x ≤
      twoSidedExitExpectationCorrected X q (h + y) y := by
  have hdown (ω : Ω) :
      twoSidedExitDownTimeCorrected X (-x) ω ≤
        twoSidedExitDownTimeCorrected X (-y) ω := by
    unfold twoSidedExitDownTimeCorrected
    refine le_iInf fun t => le_iInf fun ht => ?_
    have hthreshold : X.X t ω < -x :=
      lt_of_lt_of_le ht (neg_le_neg hxy)
    exact (iInf_le _ t).trans (iInf_le _ hthreshold)
  unfold twoSidedExitExpectationCorrected
  have hx : (h + x) - x = h := by ring
  have hy : (h + y) - y = h := by ring
  simp only [hx, hy]
  apply lintegral_mono
  intro ω
  by_cases hcase : twoSidedExitUpTimeCorrected X h ω <
      twoSidedExitDownTimeCorrected X (-x) ω
  · have h' : twoSidedExitUpTimeCorrected X h ω <
        twoSidedExitDownTimeCorrected X (-y) ω :=
      lt_of_lt_of_le hcase (hdown ω)
    simp only [if_pos hcase, if_pos h']
    exact le_rfl
  · simp only [if_neg hcase]
    exact bot_le
