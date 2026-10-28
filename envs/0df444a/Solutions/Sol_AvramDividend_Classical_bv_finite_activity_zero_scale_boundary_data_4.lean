-- Prove2me | solution 4 for AvramDividend.Classical.bv_finite_activity_zero_scale_boundary_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:15:40.606663+00:00
-- url     : https://prove2.me/submissions/4a560d41-0764-4bb9-b339-1daef684f8c7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_deriv_right_limit
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_coe_of_right_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    0 < X.drift ∧ W 0 = 1 / X.drift ∧
      derivZeroPlus W =
        (((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift ^ 2 : ℝ) : EReal) := by
  refine ⟨(bv_standing_drift_pos X hX hBV).1, ?_, ?_⟩
  · exact bv_scale_origin_eq_inv_drift X hX q hq W hW hBV
  · exact derivZeroPlus_eq_coe_of_right_tendsto W _
      (bv_finite_activity_scale_deriv_right_limit X hX q hq W hW hBV hFinite)
