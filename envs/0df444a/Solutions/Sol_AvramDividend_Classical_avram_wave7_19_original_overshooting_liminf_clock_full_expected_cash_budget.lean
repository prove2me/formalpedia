-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_overshooting_liminf_clock_full_expected_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:33:12.274016+00:00
-- url     : https://prove2.me/submissions/49215de0-0286-4835-985a-18e5c8237e65

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonmonotone_liminf_clock_full_expected_cash_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Clip overshooting source clocks at ruin, preserving all payable dividend mass. -/
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
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, (∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  classical
  let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => min (ruinTime X x D ω) (τ n ω)
  have hσmeas : ∀ n, Measurable (σ n) :=
    fun n => (ruinTime_measurable X x D hD).min (hτmeas n)
  have hσliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, σ (n + k) ω) = ruinTime X x D ω := by
    filter_upwards [hLiminfLower] with ω hω
    let r : ℝ≥0∞ := ruinTime X x D ω
    have htail (n : ℕ) :
        (⨅ k : ℕ, min r (τ (n + k) ω)) =
          min r (⨅ k : ℕ, τ (n + k) ω) := by
      apply le_antisymm
      · apply le_inf
        · exact (iInf_le (fun k : ℕ => min r (τ (n + k) ω)) 0).trans
            (min_le_left r (τ (n + 0) ω))
        · refine le_iInf (fun k => ?_)
          exact (iInf_le (fun j : ℕ => min r (τ (n + j) ω)) k).trans
            (min_le_right r (τ (n + k) ω))
      · refine le_iInf (fun k => ?_)
        exact min_le_min_left r
          (iInf_le (fun j : ℕ => τ (n + j) ω) k)
    calc
      (⨆ n : ℕ, ⨅ k : ℕ, σ (n + k) ω) =
          (⨆ n : ℕ, min r (⨅ k : ℕ, τ (n + k) ω)) := by
            apply iSup_congr
            intro n
            change (⨅ k : ℕ, min r (τ (n + k) ω)) =
              min r (⨅ k : ℕ, τ (n + k) ω)
            exact htail n
      _ = min r (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω) := by
        rw [inf_iSup_eq]
      _ = ruinTime X x D ω := by
        exact min_eq_left hω
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
        have hs : paymentTimes (σ n ω) ⊆ paymentTimes (τ n ω) := by
          simpa using paymentTimes_min_mono_horizon
            ⊤ (σ n ω) (τ n ω) (min_le_right _ _)
        exact ⟨hs ht.1, ht.2⟩
      _ ≤ budget := hBound n
  exact avram_wave7_19_original_nonmonotone_liminf_clock_full_expected_cash_budget
    X q x T D hD σ hσmeas hσliminfAE budget hσBudget
