-- Prove2me | solution 1 for AvramDividend.Classical.zero_reflectedSupValue_bv_finite_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:21:02.735413+00:00
-- url     : https://prove2.me/submissions/6d05a06c-d852-4479-8638-9df224789a7d

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
  rcases bv_finite_activity_zero_scale_boundary_data
      X hX q hq W hW hBV hFinite with ⟨hdpos, hW0, hWder⟩
  have hdenom : q + (X.ν (Iio (0 : ℝ))).toReal ≠ 0 := by
    exact ne_of_gt (add_pos_of_pos_of_nonneg hq ENNReal.toReal_nonneg)
  have hval : barrierValue W 0 0 =
      X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) :=
    barrierValue_zero_of_finite_jump_normalisation W q
      (X.ν (Iio (0 : ℝ))).toReal X.drift (ne_of_gt hdpos)
      hdenom hW0 hWder
  calc
    barrierSupValue X 0 q =
        ENNReal.ofReal (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) :=
      bv_finite_activity_zero_reflected_first_jump_payout
        X hX q hq hBV hFinite
    _ = ENNReal.ofReal (barrierValue W 0 0) :=
      congrArg ENNReal.ofReal hval.symm
