-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_injective_rightjump_absolute_le_canonical_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:35:24.862338+00:00
-- url     : https://prove2.me/submissions/455cfaa6-ee26-4e81-9331-2edc50e9a0cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash_strong_carrier
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The true original countable atomic correction is dominated by P4-F's literal Cash. -/
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
    (hPre : ∀ i, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ i, (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ i, w (riskProcess X x D (t i) ω) -
      w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        K * (rightLimit D (t i) ω - D (t i) ω)) :
    let μ : Measure ℝ := (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ A : Set ℝ, A.Countable ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      ((∀ i : ι, (t i : ℝ) ∈ A) →
      Function.Injective (fun i : ι => (t i : ℝ)) →
        Summable (fun i : ι => |Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) +
            w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω))|) ∧
        (∑' i : ι, |Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) +
            w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω))|) ≤
          (K - 1) *
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) := by
  obtain ⟨A, hCount, hSupport, hSubseries⟩ :=
    avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash_strong_carrier
      X x q hq D hD w hjump t ω T hT hPre hPay K hK hLocalSecant
  refine ⟨A, hCount, hSupport, ?_⟩
  intro hInA hInj
  obtain ⟨hAbs, hBound⟩ := hSubseries hInA hInj
  refine ⟨hAbs, ?_⟩
  have hEq := avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
    X x D hD q ω T
  rw [hEq] at hBound
  exact hBound
