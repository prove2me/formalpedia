-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_nonmonotone_liminf_clock_full_expected_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:27:07.135211+00:00
-- url     : https://prove2.me/submissions/6527ca6f-9920-49d2-8e52-9d4deef5de80

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ae_cofinal_random_clocks_expected_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_any_measurable_clock_paid_cash_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Original Stieltjes cash survives a.s. cofinal nonmonotone local-clock exhaustion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n : ℕ, Measurable (τ n))
    (hLiminf : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω) = ruinTime X x D ω)
    (budget : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, (∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  classical
  let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω
  have hσmeas : ∀ n, Measurable (σ n) := by
    intro n
    exact Measurable.iInf (fun k => hτmeas (n + k))
  have hσmono : ∀ ω, Monotone (fun n => σ n ω) := by
    intro ω n m hnm
    refine le_iInf (fun k => ?_)
    have hindex : n + ((m - n) + k) = m + k := by omega
    have hle : σ n ω ≤ τ (n + ((m - n) + k)) ω :=
      iInf_le (fun j : ℕ => τ (n + j) ω) ((m - n) + k)
    simpa only [hindex] using hle
  have hσsupAE : ∀ᵐ ω ∂P, (⨆ n, σ n ω) = ruinTime X x D ω := by
    filter_upwards [hLiminf] with ω hω
    simpa only [σ] using hω
  have hσle : ∀ n ω, σ n ω ≤ τ n ω := by
    intro n ω
    change (⨅ k : ℕ, τ (n + k) ω) ≤ τ n ω
    simpa only [Nat.add_zero] using
      (iInf_le (fun k : ℕ => τ (n + k) ω) 0)
  have hσBudget : ∀ n : ℕ,
      (∫⁻ ω, (∫⁻ t in paymentTimes (σ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
    intro n
    calc
      (∫⁻ ω, (∫⁻ t in paymentTimes (σ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤
          (∫⁻ ω, (∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) := by
        apply lintegral_mono
        intro ω
        apply lintegral_mono_set
        intro t ht
        have hp : 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ n ω) := ht.1
        refine ⟨?_, ht.2⟩
        change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < τ n ω)
        rcases hp.2 with hz | hlt
        · exact ⟨hp.1, Or.inl hz⟩
        · exact ⟨hp.1, Or.inr (lt_of_lt_of_le hlt (hσle n ω))⟩
      _ ≤ budget := hBound n
  exact avram_wave7_19_original_ae_cofinal_random_clocks_expected_cash_budget
    X q x T D hD σ hσmono hσsupAE
    (fun n => avram_wave7_19_original_any_measurable_clock_paid_cash_measurable
      D hD (σ n) (hσmeas n) q T)
    budget hσBudget
