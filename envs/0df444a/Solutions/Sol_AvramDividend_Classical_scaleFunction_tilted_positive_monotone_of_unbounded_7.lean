-- Prove2me | solution 7 for AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T23:26:33.231922+00:00
-- url     : https://prove2.me/submissions/dbbb49f5-a581-4486-b365-cff8a5e753a5

import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Extract a positive monotone Esscher normalisation from the unbounded
variation scale function and the normalised monotonicity theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : ¬ X.BoundedVariation) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  have hpos := scaleFunction_strict_pos_of_unbounded_variation X q W hW hbv
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hbv q hq
  obtain ⟨hmono, _⟩ :=
    unbounded_esscher_tilted_scale_monotone_uniform_bound
      X q hq W hW hbv φ hφ hroot
      (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (by intro x hx; rfl)
  refine ⟨hpos, ⟨φ, hφ, ?_⟩⟩
  simpa only [neg_mul] using hmono
