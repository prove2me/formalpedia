-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_turn8c_original_B_L1_from_true_strict_cash_budget_of_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:17:21.228873+00:00
-- url     : https://prove2.me/submissions/fef30642-9f9d-476b-adb0-23c12f8d8ce6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The authentic strict stopped dividend cash plus surviving terminal is
nonnegative. A finite signed physical source B, if measurable and almost surely
nonpositive, is automatically L1 once its cash budget has a centred L1
martingale and an L1 positive error. No global derivative bound is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
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
  intro n
  have hKint : Integrable
      (fun ω : Ω => w x + M n ω + max (Err n ω) 0) P := by
    exact ((integrable_const (w x)).add (hM n)).add (hErr n)
  refine Integrable.mono' hKint (hBMeas n) ?_
  filter_upwards [hBNeg n, hPayPos n, hPath n] with ω hNeg hPos hBudget
  have hLower :
      -(w x + M n ω + max (Err n ω) 0) ≤ B n ω := by
    linarith
  have hKPos : 0 ≤ w x + M n ω + max (Err n ω) 0 := by
    linarith
  have hBound :
      -B n ω ≤ w x + M n ω + max (Err n ω) 0 := by
    linarith
  simpa only [Real.norm_eq_abs, abs_of_nonpos hNeg,
    abs_of_nonneg hKPos] using hBound
