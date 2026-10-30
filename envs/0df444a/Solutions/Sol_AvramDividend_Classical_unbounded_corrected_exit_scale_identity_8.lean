-- Prove2me | solution 8 for AvramDividend.Classical.unbounded_corrected_exit_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T05:20:46.603133+00:00
-- url     : https://prove2.me/submissions/3fe3f707-5325-4b2e-b2ad-60ca2b9d7e7e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

-- 6d39 via decomp 0: Proved stopped-balance ratio + Open stopped-scale identity.
-- The stopped identity (aed) is the unfolded integral form; it is definitionally
-- the Expectation balance the Proved ratio lemma consumes, so `exact` bridges it.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectationCorrected X q a x =
      ENNReal.ofReal (W x / W a) := by
  have hBalance :=
    AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  exact
    AvramDividend.Classical.chat01_unbounded_corrected_exit_ratio_of_stopped_balance
      X q hq W hW hnbv a x ha hx hxa hBalance
