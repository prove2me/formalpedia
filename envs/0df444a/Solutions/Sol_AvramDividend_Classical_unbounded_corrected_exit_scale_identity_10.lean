-- Prove2me | solution 10 for AvramDividend.Classical.unbounded_corrected_exit_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:27:13.45116+00:00
-- url     : https://prove2.me/submissions/4442701a-fc50-4af2-aced-dcc9cad6a706

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_expectation_scale_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

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
  -- Reduction: Proved c59bf6d7 turns a stopped-scale balance into the
  -- corrected-exit ratio. Supply the balance pointwise from Open 2dcc8bcc
  -- (verbatim binders). Sketch-shaped until 2dcc8bcc is Proved.
  have hBal : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by
    intro a x ha hx0 hxa
    exact AvramDividend.Classical.chat04_unbounded_two_sided_exit_expectation_scale_identity
      X q hq W hW hnbv a x ha hx0 hxa
  exact AvramDividend.Classical.chat01_unbounded_corrected_exit_ratio_of_stopped_balance
    X q hq W hW hnbv a x ha hx hxa (hBal a x ha hx hxa)
