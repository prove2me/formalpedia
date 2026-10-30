-- Prove2me | solution 11 for AvramDividend.Classical.unbounded_tilted_positive_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:14:26.349981+00:00
-- url     : https://prove2.me/submissions/26203368-2046-4e76-868e-d9032eb9bc80

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

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
  have hMain :=
    AvramDividend.Classical.unbounded_positive_tilt_of_corrected_exit
      X q hq W hW hnbv hExit
  obtain ⟨hpos, φ, hφ, hroot, hmono⟩ := hMain
  have hmono' : MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
    simpa [neg_mul] using hmono
  exact ⟨hpos, φ, hφ, hmono'⟩
