-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_turn8b_original_B_L1_from_true_strict_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:08:18.722905+00:00
-- url     : https://prove2.me/submissions/2aeea207-7ab2-4ed5-a81a-8f09d4b48094

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn8c_original_B_L1_from_true_strict_cash_budget_of_probability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original spectrally negative Levy record carries the probability
instance needed by the two-sided strict cash budget L1 squeeze. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T) (S : ℝ≥0)
    (hS : S = ⟨T, hT⟩) (δ : ℕ → ℝ)
    (Pay M B Err : ℕ → Ω → ℝ)
    (hPayExact : ∀ n ω, Pay n ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
         Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0))
    (hM : ∀ n, Integrable (M n) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBMeas : ∀ n, AEStronglyMeasurable (B n) P)
    (hBNeg : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPayPos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Pay n ω)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      Pay n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0) :
    ∀ n, Integrable (B n) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  exact avram_p3_grid4_turn8c_original_B_L1_from_true_strict_cash_budget_of_probability
    X q w x D T hT S hS δ Pay M B Err
    hPayExact hM hErr hBMeas hBNeg hPayPos hPath
