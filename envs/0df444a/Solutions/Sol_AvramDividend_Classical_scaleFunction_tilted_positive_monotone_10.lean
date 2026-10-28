-- Prove2me | solution 10 for AvramDividend.Classical.scaleFunction_tilted_positive_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:22:00.394462+00:00
-- url     : https://prove2.me/submissions/0c191087-ec36-48dc-9564-38fb982af3ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  by_cases hbv : X.BoundedVariation
  · exact AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_bv
      X hX q hq W hW hbv
  · exact AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_corrected_exit
      X hX q hq W hW
      (fun a x ha hx0 hxa =>
        AvramDividend.Classical.two_sided_exit_before_ruin_identity_corrected
          X hX q hq W hW a x ha hx0 hxa)
