-- Prove2me | solution 11 for AvramDividend.Classical.unbounded_esscher_root_exit_decay
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:38:40.535981+00:00
-- url     : https://prove2.me/submissions/b9030aeb-c848-4647-ab01-fcb30864d51e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
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
      W x ≤ Real.exp (-φ * (y - x)) * W y := by
  -- Step 1: stopped-scale balance in expectation form (Open in-mission premise).
  have hBal : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by
    intro a x ha hx0 hxa
    have h := AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
      X q hq W hW hnbv a x ha hx0 hxa
    unfold twoSidedExitExpectation twoSidedExitUpTime twoSidedExitDownTime at *
    exact h
  -- Step 2: convert the balance to the corrected exit ratio (Proved bridge).
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx0 hxa
    exact AvramDividend.Classical.chat01_unbounded_corrected_exit_ratio_of_stopped_balance
      X q hq W hW hnbv a x ha hx0 hxa (hBal a x ha hx0 hxa)
  -- Step 3: fixed-root decay from the corrected identity (Proved bridge),
  -- with exponent parenthesization bridge: supplied form is exp (-(φ*(y-x))),
  -- target form is exp (-φ*(y-x)); equal by ring (neg_mul).
  have hmain := AvramDividend.Classical.unbounded_fixedroot_decay_of_corrected_exit_identity
    X q hq W hW hnbv φ hφ hroot hExit
  intro x y hx hxy
  have h := hmain x y hx hxy
  have hexp : (-(φ * (y - x))) = (-φ * (y - x)) := by ring
  rw [hexp] at h
  exact h
