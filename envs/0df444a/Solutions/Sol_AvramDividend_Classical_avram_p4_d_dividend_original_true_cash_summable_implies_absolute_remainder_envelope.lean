-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_true_cash_summable_implies_absolute_remainder_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:48:14.399522+00:00
-- url     : https://prove2.me/submissions/a82321d1-b526-4d6c-8771-4d6554369363

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_right_atom_cash_to_real
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_absolute_remainder_cash_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original true stopped singleton cash dominates the absolute right-payment remainder. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    {ι : Type*} (t : ι → ℝ≥0) (ω : Ω) (T : ℝ≥0)
    (hT : ∀ i : ι, t i ≤ T)
    (hPre : ∀ i : ι, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ i : ι, (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hCashSummable : Summable (fun i : ι =>
      (((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {(t i : ℝ)} *
      (if (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * (t i : ℝ)))) else 0)).toReal))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
        w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
          K * (rightLimit D (t i) ω - D (t i) ω)) :
    Summable (fun i : ι => |Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))|) ∧
    (∑' i : ι, |Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))|) ≤
      (∑' i : ι, (K - 1) *
        ((((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {(t i : ℝ)} *
          (if (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * (t i : ℝ)))) else 0)).toReal)) := by
  have hPayNonneg : ∀ i : ι, 0 ≤ rightLimit D (t i) ω - D (t i) ω := by
    intro i
    exact sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD ω (t i))
  have hWeights : ∀ i : ι,
      (((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {(t i : ℝ)} *
        (if (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * (t i : ℝ)))) else 0)).toReal =
        Real.exp (-(q * (t i : ℝ))) *
          (rightLimit D (t i) ω - D (t i) ω) := by
    intro i
    have hi :=
      avram_p4_d_dividend_original_stopped_right_atom_cash_to_real
        X x D hD ω T (t i) (hT i) (hPayNonneg i) q
    simpa only [if_pos (hPay i), mul_comm] using hi
  have hPhysicalSummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) * (rightLimit D (t i) ω - D (t i) ω)) :=
    hCashSummable.congr hWeights
  obtain ⟨hAbs, hBound⟩ :=
    avram_p4_d_dividend_original_rightjump_absolute_remainder_cash_envelope
      X x D w q hjump t ω hPre K hK hPayNonneg hPhysicalSummable hLocalSecant
  refine ⟨hAbs, ?_⟩
  calc
    _ ≤ (∑' i : ι, (K - 1) *
      (Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω))) := hBound
    _ = (∑' i : ι, (K - 1) *
      ((((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {(t i : ℝ)} *
        (if (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * (t i : ℝ)))) else 0)).toReal)) := by
      apply tsum_congr
      intro i
      rw [hWeights i]
