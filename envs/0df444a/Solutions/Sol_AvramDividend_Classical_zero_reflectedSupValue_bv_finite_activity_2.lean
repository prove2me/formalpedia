-- Prove2me | solution 2 for AvramDividend.Classical.zero_reflectedSupValue_bv_finite_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:43:51.17895+00:00
-- url     : https://prove2.me/submissions/7ac93ae9-c58e-49bb-9720-0d266860d408

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_first_jump_payout
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_scale_boundary_data
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_finite_jump_normalisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by
  obtain ⟨hd, hW0, hWder⟩ :=
    bv_finite_activity_zero_scale_boundary_data X hX q hq W hW hBV hFinite
  have hsum : q + (X.ν (Iio (0 : ℝ))).toReal ≠ 0 := by
    have hrate : 0 ≤ (X.ν (Iio (0 : ℝ))).toReal :=
      ENNReal.toReal_nonneg
    exact ne_of_gt (add_pos_of_pos_of_nonneg hq hrate)
  have hnormal :
      barrierValue W 0 0 =
        X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) :=
    barrierValue_zero_of_finite_jump_normalisation
      W q (X.ν (Iio (0 : ℝ))).toReal X.drift (ne_of_gt hd)
      hsum hW0 hWder
  calc
    barrierSupValue X 0 q =
        ENNReal.ofReal
          (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) :=
      bv_finite_activity_zero_reflected_first_jump_payout X hX q hq hBV hFinite
    _ = ENNReal.ofReal (barrierValue W 0 0) := by rw [hnormal]
