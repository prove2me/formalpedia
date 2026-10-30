-- Prove2me | solution 6 for AvramDividend.Classical.scaleFunction_tilted_positive_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:39:09.938924+00:00
-- url     : https://prove2.me/submissions/d1711cd5-f576-4ec5-aae1-768c5113e9d8

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Derive the standing scale-function tilt from the corrected exit identity,
    using the established bounded-variation and unbounded-variation cases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  by_cases hbv : X.BoundedVariation
  · exact scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv
  · have hExit :
        ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
          twoSidedExitExpectationCorrected X q a x =
            ENNReal.ofReal (W x / W a) := by
      intro a x ha hx0 hxa
      exact two_sided_exit_before_ruin_identity_corrected
        X hX q hq W hW a x ha hx0 hxa
    obtain ⟨hpos, φ, hφ, _hroot, hmono⟩ :=
      unbounded_positive_tilt_of_corrected_exit X q hq W hW hbv hExit
    refine ⟨hpos, φ, hφ, ?_⟩
    simpa only [neg_mul] using hmono
