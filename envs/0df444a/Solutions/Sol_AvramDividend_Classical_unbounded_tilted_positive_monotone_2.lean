-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_tilted_positive_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:55:04.287069+00:00
-- url     : https://prove2.me/submissions/bfbae49a-c76b-4b2e-92dd-b3d70d2e0437
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-!
The tilted scale-function monotonicity follows from the published
uniform-bound statement after selecting the positive Esscher root.
-/
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
  refine ⟨scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv, ?_⟩
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hnbv q hq
  refine ⟨φ, hφ, ?_⟩
  simpa only [neg_mul] using
    (unbounded_esscher_tilted_scale_monotone_uniform_bound
      X q hq W hW hnbv φ hφ hroot
      (fun x => Real.exp (-(φ * x)) * W x)
      (by intro x hx; rfl)).1
