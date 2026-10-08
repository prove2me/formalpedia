-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_derivZeroPlus_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T22:19:21.522537+00:00
-- url     : https://prove2.me/submissions/794f4911-9933-458e-828d-a1f80d2f6c26

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonneg
import Theorems.Thm_AvramDividend_Classical_deriv_global_lower_le_right_liminf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (0 : EReal) ≤ derivZeroPlus W := by
  have hderiv : ∀ x : ℝ, 0 < x → 0 ≤ deriv W x :=
    scaleDeriv_nonneg X q W hW
  simpa using (deriv_global_lower_le_right_liminf W 0 hderiv)
