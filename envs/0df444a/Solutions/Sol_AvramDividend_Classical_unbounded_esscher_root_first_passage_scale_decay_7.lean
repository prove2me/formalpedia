-- Prove2me | solution 7 for AvramDividend.Classical.unbounded_esscher_root_first_passage_scale_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T18:19:37.045989+00:00
-- url     : https://prove2.me/submissions/8f217595-3473-472b-a88d-e38249c80397

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! The corrected strict exit formula supplies the fixed-root first-passage ratio. -/
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
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  exact unbounded_fixedroot_decay_of_corrected_exit_identity
    X q hq W hW hnbv φ hφ hroot hExit
