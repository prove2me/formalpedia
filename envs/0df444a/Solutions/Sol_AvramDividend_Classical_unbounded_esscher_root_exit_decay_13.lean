-- Prove2me | solution 13 for AvramDividend.Classical.unbounded_esscher_root_exit_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:42:05.408969+00:00
-- url     : https://prove2.me/submissions/80d3e975-bf80-43a3-9a5a-85bca58dc0a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
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
  simpa only [neg_mul] using
    (AvramDividend.Classical.unbounded_fixedroot_decay_of_corrected_exit_identity
      X q hq W hW hnbv φ hφ hroot
      (fun a x ha hx0 hxa =>
        AvramDividend.Classical.unbounded_corrected_exit_scale_identity
          X q hq W hW hnbv a x ha hx0 hxa))
