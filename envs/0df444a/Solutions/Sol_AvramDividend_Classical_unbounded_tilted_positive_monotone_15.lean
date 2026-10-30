-- Prove2me | solution 15 for AvramDividend.Classical.unbounded_tilted_positive_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:19:02.154559+00:00
-- url     : https://prove2.me/submissions/85d1f5a8-193f-4749-85c6-572c99cb138e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact AvramDividend.Classical.unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  have hTilt := AvramDividend.Classical.unbounded_positive_tilt_of_corrected_exit
    X q hq W hW hnbv hExit
  obtain ⟨hpos, φ, hφ, _hroot, hmono⟩ := hTilt
  -- E01 repair (candidate 17715 TYPE_MISMATCH): hmono states MonotoneOn for
  -- `Real.exp (-(φ * x))` while the goal needs `Real.exp ((-φ) * x)`.
  -- `neg_mul : -a * b = -(a * b)` closes the gap definitionally via simp.
  refine ⟨hpos, φ, hφ, ?_⟩
  simpa [neg_mul] using hmono
