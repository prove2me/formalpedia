-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_spatial_nonmonotone_liminf_exhaustion_expected_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:58:53.780216+00:00
-- url     : https://prove2.me/submissions/0056c4dc-2dcf-4403-a048-065264be8b23

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Original ruin cash under nonmonotone spatial localisation and liminf expected bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (LocalCash : ℕ → Ω → ℝ≥0∞)
    (hLocalMeas : ∀ n : ℕ, Measurable (LocalCash n))
    (hExhaust : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
        ≤ (⨆ n : ℕ, ⨅ k : ℕ, LocalCash (n + k) ω))
    (budget : ℝ≥0∞)
    (hBudgetLiminf : (⨆ n : ℕ, ⨅ k : ℕ,
      (∫⁻ ω, LocalCash (n + k) ω ∂P)) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  classical
  let G (n : ℕ) (ω : Ω) : ℝ≥0∞ := ⨅ k : ℕ, LocalCash (n + k) ω
  let B (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hGmeas : ∀ n : ℕ, Measurable (G n) := by
    intro n
    exact Measurable.iInf (fun k => hLocalMeas (n + k))
  have hGmono : Monotone G := by
    intro n m hnm ω
    refine le_iInf (fun k => ?_)
    have hindex : n + ((m - n) + k) = m + k := by omega
    have hle : G n ω ≤ LocalCash (n + ((m - n) + k)) ω :=
      iInf_le (fun j : ℕ => LocalCash (n + j) ω) ((m - n) + k)
    simpa only [hindex] using hle
  change (∫⁻ ω, B ω ∂P) ≤ budget
  calc
    (∫⁻ ω, B ω ∂P) ≤ ∫⁻ ω, ⨆ n : ℕ, G n ω ∂P := by
      apply lintegral_mono_ae
      exact hExhaust
    _ = ⨆ n : ℕ, (∫⁻ ω, G n ω ∂P) := lintegral_iSup hGmeas hGmono
    _ ≤ ⨆ n : ℕ, ⨅ k : ℕ, (∫⁻ ω, LocalCash (n + k) ω ∂P) := by
      apply iSup_le
      intro n
      have hn : (∫⁻ ω, G n ω ∂P) ≤
          ⨅ k : ℕ, (∫⁻ ω, LocalCash (n + k) ω ∂P) := by
        apply le_iInf
        intro k
        apply lintegral_mono
        intro ω
        exact iInf_le (fun j : ℕ => LocalCash (n + j) ω) k
      exact hn.trans (le_iSup (fun j : ℕ =>
        ⨅ k : ℕ, (∫⁻ ω, LocalCash (j + k) ω ∂P)) n)
    _ ≤ budget := hBudgetLiminf
