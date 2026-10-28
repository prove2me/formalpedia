-- Prove2me | solution 11 for AvramDividend.Classical.scaleFunction_tilted_positive_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:04:31.223293+00:00
-- url     : https://prove2.me/submissions/aec3553e-974e-42a9-a0a3-5ec38054af24
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
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
  -- General bridge: split on BoundedVariation.
  -- BV branch is Proved 1c7b629b; ¬BV branch is Proved 2d7abb02 with hExit
  -- supplied pointwise from Open 6d3911f8 (verbatim binders).
  by_cases hbv : X.BoundedVariation
  · exact
      AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_bv
        X hX q hq W hW hbv
  · have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
        twoSidedExitExpectationCorrected X q a x =
          ENNReal.ofReal (W x / W a) :=
      fun a x ha hx hxa =>
        AvramDividend.Classical.unbounded_corrected_exit_scale_identity
          X q hq W hW hbv a x ha hx hxa
    exact
      AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_corrected_exit
        X hX q hq W hW hExit
