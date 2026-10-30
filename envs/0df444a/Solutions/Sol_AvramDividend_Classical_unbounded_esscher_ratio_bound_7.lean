-- Prove2me | solution 7 for AvramDividend.Classical.unbounded_esscher_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:09:34.799249+00:00
-- url     : https://prove2.me/submissions/1d56e9f9-d47f-4484-a836-20195780d68a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_ratio_bound_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ∃ (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q),
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x / W y ≤ Real.exp (-(φ * (y - x))) := by
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact AvramDividend.Classical.unbounded_corrected_exit_scale_identity X q hq W hW hnbv a x ha hx hxa
  exact AvramDividend.Classical.unbounded_esscher_ratio_bound_of_corrected_exit X q hq W hW hnbv hExit
