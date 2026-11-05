-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_cash_preruin_ruin_expectation_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:02:16.100472+00:00
-- url     : https://prove2.me/submissions/c75d40f9-715a-4669-85d6-49ad1a32a48b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_cash_preruin_ruin_L1_partition
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (s : Set Ω)
    (hs : s = {ω | τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω})
    (hsMeas : MeasurableSet s) :
    (∫ ω, Cash ω ∂P) =
      (∫ ω, s.indicator Cash ω ∂P) +
      (∫ ω, sᶜ.indicator Cash ω ∂P) ∧
    0 ≤ (∫ ω, s.indicator Cash ω ∂P) ∧
    0 ≤ (∫ ω, sᶜ.indicator Cash ω ∂P) := by
  classical
  obtain ⟨hPreI, hRuinI, hsplit⟩ :=
    avram_p4_d_dividend_original_cash_preruin_ruin_L1_partition
      X x q D τ Cash hCash hCashI s hs hsMeas
  have hCashNN :=
    avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
      X q x D τ Cash hCash
  constructor
  · calc
      (∫ ω, Cash ω ∂P) =
          (∫ ω, s.indicator Cash ω + sᶜ.indicator Cash ω ∂P) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hsplit
      _ = (∫ ω, s.indicator Cash ω ∂P) +
          (∫ ω, sᶜ.indicator Cash ω ∂P) :=
        integral_add hPreI hRuinI
  have hPreNN : ∀ ω, (0 : ℝ) ≤ s.indicator Cash ω := by
    intro ω
    by_cases hω : ω ∈ s
    · simpa only [Set.indicator_of_mem hω] using hCashNN ω
    · simp only [Set.indicator_of_notMem hω]
      exact le_refl 0
  have hRuinNN : ∀ ω, (0 : ℝ) ≤ sᶜ.indicator Cash ω := by
    intro ω
    by_cases hω : ω ∈ s
    · have hc : ω ∉ sᶜ := by simpa using hω
      simp only [Set.indicator_of_notMem hc]
      exact le_refl 0
    · have hc : ω ∈ sᶜ := by simpa using hω
      simpa only [Set.indicator_of_mem hc] using hCashNN ω
  exact ⟨integral_nonneg_of_ae (Filter.Eventually.of_forall hPreNN),
    integral_nonneg_of_ae (Filter.Eventually.of_forall hRuinNN)⟩
