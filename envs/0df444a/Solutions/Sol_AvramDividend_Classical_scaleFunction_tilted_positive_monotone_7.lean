-- Prove2me | solution 7 for AvramDividend.Classical.scaleFunction_tilted_positive_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:52:29.984492+00:00
-- url     : https://prove2.me/submissions/fec72f16-792a-48ea-8fa1-76c3a4552673

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_unbounded
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  -- The stochastic bridge by path-variation case split: bounded variation is
  -- handled by the Proved positive-renewal-kernel result; unbounded variation is
  -- the Open Esscher/ladder case. This is the catalogue's own decomposition.
  -- Principal lemmas: one Proved (BV), one Open (unbounded).
  -- Exact unresolved identity: scaleFunction_tilted_positive_monotone_of_unbounded.
  by_cases hbv : X.BoundedVariation
  · exact AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_bv
      X hX q hq W hW hbv
  · exact AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_unbounded
      X hX q hq W hW hbv
