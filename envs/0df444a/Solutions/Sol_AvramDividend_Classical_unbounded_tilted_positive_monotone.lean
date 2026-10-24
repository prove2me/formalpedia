-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_tilted_positive_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T06:50:10.324155+00:00
-- url     : https://prove2.me/submissions/18bfb7f8-3569-46bf-9b6b-a0f167ca9d05
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_first_passage_scale_decay
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
  have hpos := scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hnbv q hq
  have hdecay : ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-φ * (y - x)) * W y := by
    intro x y hx hxy
    simpa only [neg_mul] using
      (unbounded_esscher_root_first_passage_scale_decay
        X q hq W hW hnbv φ hφ hroot x y hx hxy)
  exact ⟨hpos, φ, hφ, exit_decay_implies_tilted_monotone W φ hdecay⟩
