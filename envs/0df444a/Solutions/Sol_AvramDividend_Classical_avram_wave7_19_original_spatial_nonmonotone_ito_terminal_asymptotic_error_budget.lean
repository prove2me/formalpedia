-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_spatial_nonmonotone_ito_terminal_asymptotic_error_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:05:07.274346+00:00
-- url     : https://prove2.me/submissions/7d71dc89-6b7e-4844-825e-1fc696309564

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Direct diagonal Fatou closure for source spatial stopped Ito with terminal errors. -/
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
    (Terminal : NNReal → ℕ → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (hStoppedTail : ∀ (ε : NNReal), 0 < ε → budget < ⊤ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫⁻ ω, LocalCash n ω + Terminal ε n ω ∂P)
          ≤ budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  classical
  let E (n : ℕ) : ℝ≥0∞ := ∫⁻ ω, LocalCash n ω ∂P
  have hBound : (⨆ m : ℕ, ⨅ k : ℕ, E (m + k)) ≤ budget := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hbudget
    obtain ⟨N, hN⟩ := hStoppedTail ε hε hbudget
    apply iSup_le
    intro m
    calc
      (⨅ k : ℕ, E (m + k)) ≤ E (m + N) :=
        iInf_le (fun k : ℕ => E (m + k)) N
      _ ≤ (∫⁻ ω, LocalCash (m + N) ω + Terminal ε (m + N) ω ∂P) := by
        dsimp [E]
        apply lintegral_mono
        intro ω
        calc
          LocalCash (m + N) ω = LocalCash (m + N) ω + 0 :=
            (add_zero _).symm
          _ ≤ _ := add_le_add_right
            (bot_le : (0 : ℝ≥0∞) ≤ Terminal ε (m + N) ω) _
      _ ≤ budget + ENNReal.ofNNReal ε := hN (m + N) (by omega)
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
    _ ≤ budget := hBound
