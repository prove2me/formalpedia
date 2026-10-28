-- Prove2me | solution 19 for AvramDividend.Classical.unbounded_esscher_root_first_passage_scale_decay
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:15:11.9343+00:00
-- url     : https://prove2.me/submissions/98671c9b-e24e-436a-9c88-9a33a1c860f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-(φ * (y - x))) * W y := by
  -- Repair of candidate 17725 CE (E01 TYPE_MISMATCH): the failed source
  -- stated this goal as `-φ * (y - x)` (i.e. `(-φ) * (y - x)`), while both
  -- the authoritative target and Proved f0963971 use `-(φ * (y - x))`.
  -- Restoring the exact authoritative header makes the final `exact` close
  -- definitionally; no `neg_mul` bridge is needed.
  have hBal : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by
    intro a x ha hx0 hxa
    exact AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
      X q hq W hW hnbv a x ha hx0 hxa
  have hCorr : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx0 hxa
    exact AvramDividend.Classical.chat01_unbounded_corrected_exit_ratio_of_stopped_balance
      X q hq W hW hnbv a x ha hx0 hxa (hBal a x ha hx0 hxa)
  exact AvramDividend.Classical.unbounded_fixedroot_decay_of_corrected_exit_identity
    X q hq W hW hnbv φ hφ hroot hCorr
