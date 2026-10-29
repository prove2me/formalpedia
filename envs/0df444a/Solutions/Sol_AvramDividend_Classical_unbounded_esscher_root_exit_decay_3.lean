-- Prove2me | solution 3 for AvramDividend.Classical.unbounded_esscher_root_exit_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:15:55.94418+00:00
-- url     : https://prove2.me/submissions/b5b81ebd-64ac-4adf-8833-fbde3c102e96

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_first_passage_scale_decay

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
The alternative exponential exit-decay milestone is propositionally
identical to the first-passage scale decay milestone. This reduction
isolates the latter as the only Open source-level dependency.
-/
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
  intro x y hx hxy
  simpa only [neg_mul] using
    unbounded_esscher_root_first_passage_scale_decay
      X q hq W hW hnbv φ hφ hroot x y hx hxy
