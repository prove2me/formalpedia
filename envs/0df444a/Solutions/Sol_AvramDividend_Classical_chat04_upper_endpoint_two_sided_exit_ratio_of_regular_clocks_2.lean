-- Prove2me | solution 2 for AvramDividend.Classical.chat04_upper_endpoint_two_sided_exit_ratio_of_regular_clocks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:42:10.120995+00:00
-- url     : https://prove2.me/submissions/93b27a40-4f29-4998-87f8-14049d838e0b

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_two_sided_exit_expectation_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Mathlib.Algebra.Order.Field.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hup0 : ∀ᵐ ω ∂P, twoSidedExitUpTime X 0 ω = 0)
    (hdownpos : ∀ᵐ ω ∂P,
      0 < twoSidedExitDownTime X (-a) ω) :
    twoSidedExitExpectation X q a a =
      ENNReal.ofReal (W a / W a) := by
  rw [AvramDividend.Classical.chat04_upper_endpoint_two_sided_exit_expectation_one X q a hup0
      hdownpos,
    div_self (AvramDividend.Classical.scaleFunction_strict_pos_of_standing X hX q hq W hW a ha).ne',
    ENNReal.ofReal_one]
