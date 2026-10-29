-- Prove2me | solution 4 for AvramDividend.Classical.scaleFunction_tilted_positive_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:11:40.555142+00:00
-- url     : https://prove2.me/submissions/265654a0-7e8c-465a-ad47-d1dd5ee3127c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_unbounded
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  by_cases hbv : X.BoundedVariation
  · exact scaleFunction_tilted_positive_monotone_of_bv
      X hX q hq W hW hbv
  · exact scaleFunction_tilted_positive_monotone_of_unbounded
      X hX q hq W hW hbv
