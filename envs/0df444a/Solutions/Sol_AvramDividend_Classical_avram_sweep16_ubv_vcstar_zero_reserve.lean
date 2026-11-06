-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_ubv_vcstar_zero_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:02:29.036571+00:00
-- url     : https://prove2.me/submissions/ac622911-f21e-4681-9f1d-7442c030daa6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_on_Iic_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- The unbounded-variation scale function vanishes at the origin, and the
   source-exact c-star scaling preserves this boundary value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    vcstar W 0 = 0 := by
  have hW0 : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hBV q hq W hW
  have hbound : (0 : ℝ) ≤ (cstar W).toReal := ENNReal.toReal_nonneg
  calc
    vcstar W 0 = divE (W 0) (scaleDeriv W (cstar W).toReal) :=
      vcstar_eq_scaledW_on_Iic_cstar W hW.1 0 hbound
    _ = 0 := by simp [divE, hW0]
