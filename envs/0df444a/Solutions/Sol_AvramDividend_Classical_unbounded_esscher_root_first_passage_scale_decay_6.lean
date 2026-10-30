-- Prove2me | solution 6 for AvramDividend.Classical.unbounded_esscher_root_first_passage_scale_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:40:39.296579+00:00
-- url     : https://prove2.me/submissions/a2305411-581f-4860-8d07-8941f4a6f74d

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_scale_decay_of_corrected_exit_estimates
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! The corrected-exit fluctuation identity yields the exact Esscher scale decay. -/
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
  have hpos : ∀ y : ℝ, 0 < y → 0 < W y :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  have hBound : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x ≤
        ENNReal.ofReal (Real.exp (-(φ * (a - x)))) := by
    intro a x ha hx hxa
    exact corrected_exit_exp_bound_at_positive_root
      X q hq φ hφ hroot a x ha hx hxa
  exact unbounded_fixedroot_scale_decay_of_corrected_exit_estimates
    X q W hpos φ hExit hBound
