-- Prove2me | solution 4 for AvramDividend.Classical.scaleDeriv_eventually_ge_exp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:10:39.406291+00:00
-- url     : https://prove2.me/submissions/f9e50c05-e2f2-474e-a349-ae4bc3a2bc5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_eventually_ge_exp_of_bv_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_eventually_ge_exp_of_corrected_exit_and_C1
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ c : ℝ, 0 < φ ∧ 0 < c ∧
      ∀ᶠ x in Filter.atTop, c * Real.exp (φ * x) ≤ deriv W x := by
  by_cases hbv : X.BoundedVariation
  · exact AvramDividend.Classical.scaleDeriv_eventually_ge_exp_of_bv_standing
      X hX q hq W hW hbv
  · exact
      AvramDividend.Classical.scaleDeriv_eventually_ge_exp_of_corrected_exit_and_C1
        X hX q hq W hW
        (fun a x ha hx0 hxa =>
          AvramDividend.Classical.two_sided_exit_before_ruin_identity_corrected
            X hX q hq W hW a x ha hx0 hxa)
        (AvramDividend.Classical.scaleFunction_contDiff_one_of_standing
          X hX q hq W hW)
