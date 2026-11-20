-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_physical_early_first_ruin_mark_original_rightclosed_stieltjes_cash_zero_without_future_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:17:17.44318+00:00
-- url     : https://prove2.me/submissions/30a52858-189b-4893-bd33-1913c3149789

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_any_finite_barrier_dividendMeasure_Iic_eq_cumulative
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (q : ℝ) :
    (∫⁻ s in paymentTimes
        (ruinTime X (1 / 10 : ℝ)
          (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω) ∩
        Iic (σ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)) = 0 := by
  have hBound : ∀ s : ℝ≥0, s ≤ σ →
      X.X s ω ≤ (1 / 5 : ℝ) - (1 / 10 : ℝ) := by
    intro s hs
    rw [hPath s]
    have hB := abs_lt.mp (hTube s hs)
    have hN : 0 ≤ (N s : ℝ) := Nat.cast_nonneg _
    norm_num at *
    linarith
  have hDzero : barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ) σ ω = 0 :=
    barrierStrategy_zero_before_upcrossing
      X (1 / 10 : ℝ) (1 / 5 : ℝ) σ ω hBound
  have hmeas :
      dividendMeasure (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω
        (Iic (σ : ℝ)) = 0 := by
    rw [avram_jump6_A_original_any_finite_barrier_dividendMeasure_Iic_eq_cumulative
      X (1 / 10 : ℝ) (1 / 5 : ℝ) (by norm_num) ω σ, hDzero]
    simp
  have hsub : paymentTimes
      (ruinTime X (1 / 10 : ℝ)
        (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
        ∩ Iic (σ : ℝ) ⊆ Iic (σ : ℝ) := inter_subset_right
  have hzero :
      dividendMeasure (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω
        (paymentTimes (ruinTime X (1 / 10 : ℝ)
          (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
          ∩ Iic (σ : ℝ)) = 0 := by
    exact le_antisymm ((measure_mono hsub).trans hmeas.le) bot_le
  have hr : (dividendMeasure
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω).restrict
        (paymentTimes (ruinTime X (1 / 10 : ℝ)
          (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
          ∩ Iic (σ : ℝ)) = 0 :=
    Measure.restrict_eq_zero.mpr hzero
  change (∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω).restrict (paymentTimes (ruinTime X (1 / 10 : ℝ) (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω) ∩ Iic (σ : ℝ))) = 0
  rw [hr]
  simp
