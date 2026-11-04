-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:58:38.093937+00:00
-- url     : https://prove2.me/submissions/1b0b31e1-e1ae-41bf-b1ba-b83d5bf3d8dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_eligible_rightjump_signed_absolute_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original paymentTimes membership already guarantees each real payment index is initial or strictly pre-ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : ι → ℝ≥0) (ω : Ω) (T : ℝ≥0)
    (hT : ∀ i, t i ≤ T)
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
    Summable J ∧ (∑' i : ι, J i) ≤ 0 ∧
      Summable (fun i : ι => |J i|) ∧
      (∑' i : ι, |J i|) ≤
        (K - 1) * (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  have hPre : ∀ i : ι, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω := by
    intro i
    rcases avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
      X x D ω (t i : ℝ) (hPay i) with hz | ⟨_, hlt⟩
    · left
      simpa only [Real.toNNReal_coe] using hz
    · right
      simpa only [Real.toNNReal_coe] using hlt
  obtain ⟨hSum, hNeg, hAbs, hBound⟩ :=
    avram_p4_d_dividend_original_all_eligible_rightjump_signed_absolute_budget
      X x q hq D hD w hjump t ω T hT hPre hPay hInj K hK hLocalSecant
  refine ⟨hSum, hNeg, hAbs, ?_⟩
  have hEq :=
    avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop X x D hD q ω T
  rw [hEq] at hBound
  exact hBound
