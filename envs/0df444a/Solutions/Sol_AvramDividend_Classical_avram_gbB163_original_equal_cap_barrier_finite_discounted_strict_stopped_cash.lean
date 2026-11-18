-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:34:28.65432+00:00
-- url     : https://prove2.me/submissions/f2453f40-ad9a-4c45-a1f6-b98fa05bbe6b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB161_original_strict_prepayment_times_are_nonnegative_horizon_bounded
import Theorems.Thm_AvramDividend_Classical_avram_gbB162_original_equal_cap_barrier_measure_full_nonpositive_to_T_mass
import Theorems.Thm_AvramDividend_Classical_avram_gbB158_finite_positive_horizon_measure_implies_finite_discounted_stopped_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original finite-horizon cap barrier stopped cash is always finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in paymentTimes (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)) ≠ ⊤ := by
  let D := barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)
  let μ := dividendMeasure D ω
  have hFull := avram_gbB162_original_equal_cap_barrier_measure_full_nonpositive_to_T_mass
    X (1 / 8 : ℝ) ω T
  have hSub : Icc (0 : ℝ) (T : ℝ) ⊆ Iic (T : ℝ) := by
    intro z hz
    exact hz.2
  have hMass : μ (Icc (0 : ℝ) (T : ℝ)) ≠ ⊤ := by
    have hLe := measure_mono hSub (μ := μ)
    have hTop : μ (Icc (0 : ℝ) (T : ℝ)) < ⊤ := by
      calc
        _ ≤ μ (Iic (T : ℝ)) := hLe
        _ = ENNReal.ofReal (D T ω) := hFull
        _ < ⊤ := by simp
    exact ne_of_lt hTop
  have hSupport :=
    avram_gbB161_original_strict_prepayment_times_are_nonnegative_horizon_bounded
      (ruinTime X (1 / 8 : ℝ) D ω) T
  exact
    avram_gbB158_finite_positive_horizon_measure_implies_finite_discounted_stopped_cash
      μ q (T : ℝ) hq T.property
      (paymentTimes (ruinTime X (1 / 8 : ℝ) D ω) ∩ Iio (T : ℝ))
      hSupport hMass
