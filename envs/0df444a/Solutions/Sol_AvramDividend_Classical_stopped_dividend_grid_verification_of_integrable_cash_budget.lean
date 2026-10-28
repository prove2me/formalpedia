-- Prove2me | solution 1 for AvramDividend.Classical.stopped_dividend_grid_verification_of_integrable_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:01:36.675555+00:00
-- url     : https://prove2.me/submissions/c1ef9b67-b5f1-490e-9171-61c25cae0cc9

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.Finset.Range
import Theorems.Thm_AvramDividend_Classical_exponential_levy_grid_cash_stieltjes_limit_le_initial
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_real_cash_prefix_measurable_of_strategy
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_cash_prefixes_nonnegative_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
/-- Stopped Stieltjes verification under integrable future-dependent interval cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (u cash : ℕ → Ω → ℝ) (w : ℝ → ℝ) (q x : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0)
    (hCashEq : ∀ (k : ℕ) (ω : Ω), cash k ω =
      (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩ Ico (k : ℝ) ((k : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : ∀ k, Integrable (cash k) P)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = x)
    (hVI : ∀ k, Integrable (fun ω => Real.exp (-(q * (s k : ℝ))) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      (P[(cash k) | 𝓕 (s k)]) ω +
      (P[(fun η => Real.exp (-(q * (s (k + 1) : ℝ))) * w (u (k + 1) η)) | 𝓕 (s k)]) ω ≤
      Real.exp (-(q * (s k : ℝ))) * w (u k ω))
    (hterminal : ∀ n : ℕ, 0 ≤ ∫ ω, Real.exp (-(q * (s n : ℝ))) * w (u n ω) ∂P) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  have hPrefixI : ∀ n, Integrable (fun ω : Ω => ∑ k ∈ Finset.range n, cash k ω) P := by
    intro n
    exact integrable_finset_sum (Finset.range n) (fun k _ => hCashI k)
  have hCashNN : ∀ ω : Ω, ∀ k : ℕ, 0 ≤ cash k ω := by
    intro ω k
    rw [hCashEq k ω]
    exact ENNReal.toReal_nonneg
  have hPrefixNN : ∀ n, 0 ≤ᵐ[P] (fun ω => ∑ k ∈ Finset.range n, cash k ω) := by
    intro n
    filter_upwards [] with ω
    exact (nonnegative_real_cash_prefixes_nonnegative_monotone
      (fun k => cash k ω) (hCashNN ω)).1 n
  have hPrefixAE : ∀ n, AEMeasurable (fun ω : Ω =>
      ENNReal.ofReal (∑ k ∈ Finset.range n, cash k ω)) P := by
    intro n
    simpa only [hCashEq] using (stopped_discounted_real_cash_prefix_measurable_of_strategy
      X q x D hD T n).aemeasurable
  have hMono : ∀ᵐ ω ∂P, Monotone (fun n : ℕ =>
      ENNReal.ofReal (∑ k ∈ Finset.range n, cash k ω)) := by
    filter_upwards [] with ω
    exact (nonnegative_real_cash_prefixes_nonnegative_monotone
      (fun k => cash k ω) (hCashNN ω)).2
  have hZ : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ⨆ n : ℕ, ENNReal.ofReal (∑ k ∈ Finset.range n, cash k ω) := by
    filter_upwards [] with ω
    have hz := stopped_discounted_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy
      D hD q hq (ruinTime X x D ω) T ω
    simpa only [hCashEq] using (le_of_eq hz)
  exact exponential_levy_grid_cash_stieltjes_limit_le_initial
    P 𝓕 s hs hs0 u cash w q x hu0 hCashI hVI hstep hterminal
    hPrefixI hPrefixNN hPrefixAE hMono
    (fun ω => ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
    hZ