-- Prove2me | solution 14 for AvramDividend.Classical.unbounded_tilted_positive_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:43:19.454979+00:00
-- url     : https://prove2.me/submissions/0f7fe535-411b-4de4-bfd9-33ef831a21f1

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
  obtain ⟨hpos, φ, hφ, _, hmono⟩ :=
    AvramDividend.Classical.unbounded_positive_tilt_of_corrected_exit
      X q hq W hW hnbv hExit
  have hbridge : (fun x : ℝ => Real.exp (-φ * x) * W x)
      = (fun x : ℝ => Real.exp (-(φ * x)) * W x) := by
    funext x
    congr 1
    congr 1
    ring
  have hmonoGoal : MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) :=
    hbridge.symm ▸ hmono
  exact ⟨hpos, φ, hφ, hmonoGoal⟩
-- repair17676b: distinct bytes, same neg_mul bridge for E01
