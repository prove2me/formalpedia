-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_ubv_zero_start_original_full_discounted_stieltjes_reward_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:12:15.59586+00:00
-- url     : https://prove2.me/submissions/66b1e9f6-2f38-43e3-8a20-6f01a77f4492

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_ubv_any_original_zero_start_instant_ruin_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 C D)
    (T : ℝ≥0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) = 0 := by
  have hruin : ∀ᵐ ω ∂P, ruinTime X 0 D ω = 0 :=
    avram_wave6_08_ubv_any_original_zero_start_instant_ruin_ae X hBV D hD.1.1
  have hzero : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by
    filter_upwards [hruin] with ω hω
    have hcap : ENNReal.ofReal (0 : ℝ) ≤ C := by simp
    have hbudget := avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget
      X 0 C hcap D hD q T ω hω
    simpa only [ENNReal.ofReal_zero, nonpos_iff_eq_zero] using hbudget
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)
        = (∫⁻ ω, (0 : ℝ≥0∞) ∂P) := lintegral_congr_ae hzero
    _ = 0 := by simp
