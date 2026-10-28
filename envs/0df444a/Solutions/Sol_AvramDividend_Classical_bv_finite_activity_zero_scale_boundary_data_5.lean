-- Prove2me | solution 5 for AvramDividend.Classical.bv_finite_activity_zero_scale_boundary_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:31:20.649199+00:00
-- url     : https://prove2.me/submissions/a78df553-cf71-4d54-8300-1352b9380c57

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_deriv_right_limit
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_coe_of_right_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
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
  refine ⟨(bv_standing_drift_pos X hX hBV).1,
    bv_scale_origin_eq_inv_drift X hX q hq W hW hBV, ?_⟩
  exact derivZeroPlus_eq_coe_of_right_tendsto W
    ((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift ^ 2)
    (bv_finite_activity_scale_deriv_right_limit
      X hX q hq W hW hBV hFinite)
