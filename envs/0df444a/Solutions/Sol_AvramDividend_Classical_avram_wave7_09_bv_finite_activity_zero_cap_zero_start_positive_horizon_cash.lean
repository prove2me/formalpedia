-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_zero_start_positive_horizon_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:04:11.652641+00:00
-- url     : https://prove2.me/submissions/3011d7d8-9347-4aeb-8426-2df45944ed4c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_first_jump_payout
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ n : ℕ, 0 <
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by
  classical
  have hD : IsAdmissibleLe X 0 0 (barrierStrategy X 0 0) := by
    simpa only [ENNReal.ofReal_zero] using
      (barrierStrategy_admissibleLe_nonnegative_barrier
        X 0 0 (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))
  have hDrift : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  have hDenom : 0 < q + (X.ν (Iio (0 : ℝ))).toReal :=
    add_pos_of_pos_of_nonneg hq ENNReal.toReal_nonneg
  have hRatio : 0 < X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) :=
    div_pos hDrift hDenom
  have hValue : 0 < dividendValue X q 0 (barrierStrategy X 0 0) := by
    rw [barrierValue_self_eq_barrierSupValue,
      bv_finite_activity_zero_reflected_first_jump_payout X hX q hq hBV hFinite]
    exact ENNReal.ofReal_pos.mpr hRatio
  by_contra hn
  have hBounds : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤ 0 := by
    intro n
    apply le_of_not_gt
    intro hp
    exact hn ⟨n, hp⟩
  have hUpper := dividendValue_le_of_uniform_truncated_bounds
    X q 0 (barrierStrategy X 0 0) hD.1 0 hBounds
  exact (not_le_of_gt hValue) hUpper
