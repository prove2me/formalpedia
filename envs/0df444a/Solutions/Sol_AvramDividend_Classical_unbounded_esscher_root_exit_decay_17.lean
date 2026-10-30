-- Prove2me | solution 17 for AvramDividend.Classical.unbounded_esscher_root_exit_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T17:14:28.167958+00:00
-- url     : https://prove2.me/submissions/a32bfb57-7533-4669-947e-76e1fb638e69

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

-- 2026-10-28b byte-distinct resubmission: same f0963971+6d3911f8 route
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-φ * (y - x)) * W y := by
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact AvramDividend.Classical.unbounded_corrected_exit_scale_identity X q hq W hW hnbv a x ha hx hxa
  have hdec : ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-(φ * (y - x))) * W y :=
    AvramDividend.Classical.unbounded_fixedroot_decay_of_corrected_exit_identity X q hq W hW hnbv φ hφ hroot hExit
  intro x y hx hxy
  have h := hdec x y hx hxy
  have e : Real.exp (-(φ * (y - x))) = Real.exp (-φ * (y - x)) := by congr 1; ring
  rwa [e] at h
