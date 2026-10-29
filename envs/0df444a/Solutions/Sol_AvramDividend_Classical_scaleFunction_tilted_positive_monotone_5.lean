-- Prove2me | solution 5 for AvramDividend.Classical.scaleFunction_tilted_positive_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:58:52.119992+00:00
-- url     : https://prove2.me/submissions/3bdea5c3-a015-48f8-a9ff-8c57f745d855

import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_unbounded
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  by_cases hbv : X.BoundedVariation
  · exact scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv
  · exact scaleFunction_tilted_positive_monotone_of_unbounded X hX q hq W hW hbv
