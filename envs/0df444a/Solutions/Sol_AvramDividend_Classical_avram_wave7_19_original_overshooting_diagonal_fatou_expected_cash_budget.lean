-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_overshooting_diagonal_fatou_expected_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:50:33.352586+00:00
-- url     : https://prove2.me/submissions/0a184b9b-eee8-4f3b-958c-4cf8f2c75d30

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_overshooting_liminf_clock_pathwise_cash_le_liminf
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_any_measurable_clock_paid_cash_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Diagonal Fatou passage for the full original ruin cash, using only liminf of stopped expectations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n : ℕ, Measurable (τ n))
    (hLiminfLower : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω))
    (budget : ℝ≥0∞)
    (hBudgetLiminf :
      (⨆ n : ℕ, ⨅ k : ℕ,
        (∫⁻ ω, (∫⁻ t in paymentTimes (τ (n + k) ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P)) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  classical
  let A (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let G (n : ℕ) (ω : Ω) : ℝ≥0∞ := ⨅ k : ℕ, A (n + k) ω
  let B (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hAmeas : ∀ n : ℕ, Measurable (A n) := by
    intro n
    exact avram_wave7_19_original_any_measurable_clock_paid_cash_measurable
      D hD (τ n) (hτmeas n) q T
  have hGmeas : ∀ n : ℕ, Measurable (G n) := by
    intro n
    exact Measurable.iInf (fun k => hAmeas (n + k))
  have hGmono : Monotone G := by
    intro n m hnm ω
    refine le_iInf (fun k => ?_)
    have hindex : n + ((m - n) + k) = m + k := by omega
    have hle : G n ω ≤ A (n + ((m - n) + k)) ω :=
      iInf_le (fun j : ℕ => A (n + j) ω) ((m - n) + k)
    simpa only [hindex] using hle
  have hpath : ∀ᵐ ω ∂P, B ω ≤ ⨆ n : ℕ, G n ω := by
    filter_upwards [hLiminfLower] with ω hω
    exact avram_wave7_19_original_overshooting_liminf_clock_pathwise_cash_le_liminf
      X q x T D ω (fun n => τ n ω) hω
  have hExpLiminf :
      (⨆ n : ℕ, ⨅ k : ℕ, (∫⁻ ω, A (n + k) ω ∂P)) ≤ budget :=
    hBudgetLiminf
  change (∫⁻ ω, B ω ∂P) ≤ budget
  calc
    (∫⁻ ω, B ω ∂P) ≤ ∫⁻ ω, ⨆ n : ℕ, G n ω ∂P := by
      apply lintegral_mono_ae
      exact hpath
    _ = ⨆ n : ℕ, (∫⁻ ω, G n ω ∂P) := lintegral_iSup hGmeas hGmono
    _ ≤ ⨆ n : ℕ, ⨅ k : ℕ, (∫⁻ ω, A (n + k) ω ∂P) := by
      apply iSup_le
      intro n
      have hn : (∫⁻ ω, G n ω ∂P) ≤
          ⨅ k : ℕ, (∫⁻ ω, A (n + k) ω ∂P) := by
        apply le_iInf
        intro k
        apply lintegral_mono
        intro ω
        exact iInf_le (fun j : ℕ => A (n + j) ω) k
      exact hn.trans (le_iSup (fun j : ℕ =>
        ⨅ k : ℕ, (∫⁻ ω, A (j + k) ω ∂P)) n)
    _ ≤ budget := hExpLiminf
