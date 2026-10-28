-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_zero_scale_boundary_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:37:24.981232+00:00
-- url     : https://prove2.me/submissions/ae47b976-ec9d-4906-b58a-5521111ca4a4

import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_of_local_volterra_derivative
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_volterra_origin_package

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
  have hpos : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  obtain ⟨hW0, G, hWcont, hG, hDer⟩ :=
    bv_finite_activity_scale_volterra_origin_package X hX q hq W hW hBV hFinite
  refine ⟨hpos, hW0, ?_⟩
  have hslope :=
    derivZeroPlus_of_local_volterra_derivative W G X.drift
      ((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift)
      hW0 hWcont hG hDer
  simpa only [div_eq_mul_inv, pow_two, mul_inv_rev, mul_assoc] using hslope
