-- Prove2me | solution 2 for AvramDividend.Classical.chat04_unbounded_zero_start_exit_ratio_of_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:32:41.087714+00:00
-- url     : https://prove2.me/submissions/4b507e08-f9ae-4590-a197-31a6ccf84da5

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_zero_start_two_sided_exit_expectation_of_near_zero
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hnear : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    twoSidedExitExpectation X q a 0 =
      ENNReal.ofReal (W 0 / W a) := by
  have hWzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation
      X hnbv q hq W hW
  calc
    twoSidedExitExpectation X q a 0 = 0 :=
      chat04_zero_start_two_sided_exit_expectation_of_near_zero
        X q a hnear
    _ = ENNReal.ofReal (W 0 / W a) := by
      simp [hWzero]
