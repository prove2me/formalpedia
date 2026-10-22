-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_zero_origin_gaussian_of_finite_small_jump_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:41:38.230414+00:00
-- url     : https://prove2.me/submissions/11a8436b-6679-45d4-a114-cd751402b94f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The stronger proved Gaussian origin theorem implies the same
origin equality under the additional finite-small-jump condition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (_hν : X.ν (Iic (-1 : ℝ)) ≠ ⊤) :
    W 0 = 0 := by
  exact scaleFunction_zero_origin_gaussian_without_standing
    X q hq W hW hσ
