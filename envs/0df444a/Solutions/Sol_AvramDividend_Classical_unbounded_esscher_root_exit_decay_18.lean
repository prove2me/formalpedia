-- Prove2me | solution 18 for AvramDividend.Classical.unbounded_esscher_root_exit_decay
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:18:57.583074+00:00
-- url     : https://prove2.me/submissions/2d5d5111-c5b2-4d6f-a3ee-9895b2ac10b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_esscher_decay_of_stopped_scale_balance
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
  -- Principal route: stopped-scale balance then direct Proved decay bridge.
  -- hBal supplies the exact balance premise for f938e327; no corrected
  -- intermediate is introduced, so the diagnostic localises to the balance
  -- construction versus the single decay application.
  have hBal : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by
    intro a x ha hx0 hxa
    have h := AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
      X q hq W hW hnbv a x ha hx0 hxa
    unfold twoSidedExitExpectation twoSidedExitUpTime twoSidedExitDownTime at *
    exact h
  have hmain := AvramDividend.Classical.chat01_unbounded_esscher_decay_of_stopped_scale_balance
    X q hq W hW hnbv φ hφ hroot hBal
  intro x y hx hxy
  have h := hmain x y hx hxy
  have hexp : (-(φ * (y - x))) = (-φ * (y - x)) := by ring
  rw [hexp] at h
  exact h
