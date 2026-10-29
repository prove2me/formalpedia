-- Prove2me | solution 3 for AvramDividend.Classical.zero_reflectedSupValue_bv_infinite_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:42:57.454615+00:00
-- url     : https://prove2.me/submissions/fdf6655d-e212-4a09-85bc-f5e5c8748123

import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_bv_infinite_activity_strict_survival_null_all_positive
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_ae_instant_ruin_of_strict_horizon_null
import Theorems.Thm_AvramDividend_Classical_scale_derivZeroPlus_top_of_bv_infinite_negative_activity
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_derivZeroPlus_top
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Infinite BV negative-jump activity forces immediate reflected zero-barrier
ruin, making both stochastic reward and analytic boundary value vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by
  have hAll := avram_ws01e_bt_new_bv_infinite_activity_strict_survival_null_all_positive
    X hX hBV hInfinite
  have hNull (t : ℝ≥0∞) (ht : 0 < t) :
      P {ω : Ω | t < barrierRuinTime X 0 ω} = 0 := by
    by_cases htTop : t = ⊤
    · simp [htTop]
    · have htNN : 0 < t.toNNReal :=
        ENNReal.toNNReal_pos (ne_of_gt ht) htTop
      have h := hAll t.toNNReal htNN
      simpa only [ENNReal.coe_toNNReal htTop] using h
  have hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0 :=
    avram_ws01e_bt_new_ae_instant_ruin_of_strict_horizon_null
      P (barrierRuinTime X 0) hNull
  have hReward : barrierSupValue X 0 q = 0 :=
    barrierSupValue_zero_of_ae_instant_ruin X 0 q hRuin
  have hSlope : derivZeroPlus W = ⊤ :=
    scale_derivZeroPlus_top_of_bv_infinite_negative_activity
      X hX q hq W hW hBV hInfinite
  have hBoundary : barrierValue W 0 0 = 0 :=
    barrierValue_zero_of_derivZeroPlus_top W hSlope
  rw [hReward, hBoundary]
  simp
