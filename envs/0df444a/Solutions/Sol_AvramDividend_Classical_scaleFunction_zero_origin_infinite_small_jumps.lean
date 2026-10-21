-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_zero_origin_infinite_small_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T02:16:30.444945+00:00
-- url     : https://prove2.me/submissions/a361aff8-55c7-403f-91a9-b496831eba85

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_psi_normalised_unbounded_small_jumps
import Theorems.Thm_AvramDividend_Classical_scaleFunction_origin_zero_of_superlinear_psi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    W 0 = 0 := by
  exact scaleFunction_origin_zero_of_superlinear_psi X q hq W hW
    (psi_normalised_unbounded_small_jumps X hσ hinf)
