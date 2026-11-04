-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_interior_diffuse_all_eligible_atomic_signed_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:58:30.720213+00:00
-- url     : https://prove2.me/submissions/2138173c-6a66-43a9-941f-f2c6c5ae915b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_interior_diffuse_countable_atomic_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_eligible_rightjump_signed_absolute_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The strictly interior diffuse control loss and all genuine right atoms have nonpositive total, with summability from true cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (A : Set ℝ) (hA : MeasurableSet A)
    (hregion : ∀ s ∈ A,
      0 < riskProcess X x D s.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (hInt : IntegrableOn
      (fun s : ℝ => Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      A (dividendMeasure D ω))
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : ι → ℝ≥0) (T : ℝ≥0)
    (hT : ∀ i, t i ≤ T)
    (hPre : ∀ i, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ i, (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : Function.Injective (fun i : ι => (t i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ i, w (riskProcess X x D (t i) ω) -
      w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        K * (rightLimit D (t i) ω - D (t i) ω)) :
    let J : ι → ℝ := fun i => Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))
    (∫ s in A, Real.exp (-(q * s)) *
      (1 - deriv w (riskProcess X x D s.toNNReal ω))
      ∂(dividendMeasure D ω)) + (∑' i : ι, J i) ≤ 0 ∧
    Summable J ∧ Summable (fun i : ι => |J i|) ∧
    (∑' i : ι, |J i|) ≤
      (K - 1) * (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  obtain ⟨hSumm, _, hAbs, hBound⟩ :=
    avram_p4_d_dividend_original_all_eligible_rightjump_signed_absolute_budget
      X x q hq D hD w hjump t ω T hT hPre hPay hInj K hK hLocalSecant
  have hJoint :=
    avram_p4_d_dividend_original_interior_diffuse_countable_atomic_signed_budget
      X x D hD q w C hw_grad ω A hA hregion hInt hjump t hPre hSumm
  refine ⟨hJoint, hSumm, hAbs, ?_⟩
  have hEq :=
    avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop X x D hD q ω T
  rw [hEq] at hBound
  exact hBound
