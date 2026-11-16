-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_nojump_tenth_clipped_cash_plus_terminal_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:06:33.369513+00:00
-- url     : https://prove2.me/submissions/7888dbf9-07e1-40e9-906a-4915889b778b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_unit_drift_zero_barrier_nojump_survives_tenth
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_unit_drift_zero_barrier_dividendMeasure_Ioc_exact
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_strict_payment_window_contains_eight_hundredths
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_restricted_discounted_Stieltjes_cash_real_lower
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift)
    (n : ℕ) (hn : 4 ≤ n) :
    let D := barrierStrategy X 0 0
    let T : ℝ := 1 / 10
    let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
    (2 / 25 + 1 / 2 : ℝ) * Real.exp (-T) ≤
      (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩
          Iio (T - T / ((n : ℝ) + 2)),
        ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
        (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) <
           ruinTime X 0 D ω then
          Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω)
         else 0) := by
  dsimp
  let D := barrierStrategy X 0 0
  have hDiv : IsDividendStrategy 𝓕 D := by
    exact barrierStrategy_isDividendStrategy_nonnegative_barrier
      X 0 0 (by norm_num) (by norm_num)
  have hSurv :
      (((1 / 10 : ℝ≥0) : ℝ≥0∞) < ruinTime X 0 D ω) :=
    avram_bvb_obstruction_unit_drift_zero_barrier_nojump_survives_tenth
      X ω hDrift hPath
  have hMass :
      (dividendMeasure D ω) (Ioc (0 : ℝ) (2 / 25 : ℝ)) =
        ENNReal.ofReal (2 / 25 : ℝ) := by
    exact avram_bvb_obstruction_original_unit_drift_zero_barrier_dividendMeasure_Ioc_exact
      X ω 1 (2 / 25 : ℝ≥0)
        (by exact_mod_cast (show (2 / 25 : ℝ) ≤ (1 : ℝ) by norm_num))
        hDrift hPath
  have hSet : Ioc (0 : ℝ) (2 / 25 : ℝ) ⊆
      paymentTimes (ruinTime X 0 D ω) ∩
        Iio ((1 / 10 : ℝ) - (1 / 10 : ℝ) / ((n : ℝ) + 2)) :=
    avram_bvb_obstruction_tenth_strict_payment_window_contains_eight_hundredths
      _ hSurv n hn
  have hTime : 0 ≤ (1 / 10 : ℝ) - (1 / 10 : ℝ) / ((n : ℝ) + 2) := by
    have hN : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hPos : 0 < (n : ℝ) + 2 := by positivity
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hPos).2
    nlinarith
  have hFin : (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩
      Iio ((1 / 10 : ℝ) - (1 / 10 : ℝ) / ((n : ℝ) + 2)),
        ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)) ≠ ⊤ := by
    simpa only [one_mul] using
      (avram_limit2_original_strict_discounted_cash_finite_all_paths
        X 1 (by norm_num) 0 D hDiv ω
        ((1 / 10 : ℝ) - (1 / 10 : ℝ) / ((n : ℝ) + 2)) hTime)
  have hCash :=
    avram_bvb_obstruction_restricted_discounted_Stieltjes_cash_real_lower
      (dividendMeasure D ω)
      (paymentTimes (ruinTime X 0 D ω) ∩
        Iio ((1 / 10 : ℝ) - (1 / 10 : ℝ) / ((n : ℝ) + 2)))
      hSet hMass hFin
  have hNonneg : 0 ≤ X.drift := by rw [hDrift]; norm_num
  have hZero :=
    (avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
      X ω 1 hNonneg (by
        intro t ht
        rw [hPath t ht]
        ring))
      (1 / 10 : ℝ≥0)
        (by exact_mod_cast (show (1 / 10 : ℝ) ≤ (1 : ℝ) by norm_num))
  have hReserve : riskProcess X 0 D (1 / 10 : ℝ≥0) ω = 0 := hZero.2
  rw [if_pos hSurv, hReserve]
  have hSum := add_le_add_right hCash
    (Real.exp (-(1 / 10 : ℝ)) * (1 / 2 : ℝ))
  simpa [add_mul, mul_comm, mul_left_comm, mul_assoc] using hSum
