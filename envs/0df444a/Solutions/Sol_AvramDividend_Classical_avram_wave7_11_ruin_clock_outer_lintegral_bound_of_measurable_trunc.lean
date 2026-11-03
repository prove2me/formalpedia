-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_ruin_clock_outer_lintegral_bound_of_measurable_trunc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:39:00.222582+00:00
-- url     : https://prove2.me/submissions/5f36268c-b372-4764-89f5-64146fd849ac

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Measurable original-path truncated rewards permit monotone convergence
    of the expected discounted Stieltjes payoff through the ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q T : ℝ) (B : ℝ≥0∞)
    (hMeas : ∀ n : ℕ, Measurable (fun ω =>
      ∫⁻ t in paymentTimes (min (σ ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (σ ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ t in paymentTimes (min (σ ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hFmeas (n : ℕ) : Measurable (F n) := hMeas n
  have hFmono : Monotone F := by
    intro n m hnm ω
    apply MeasureTheory.lintegral_mono_set
    intro t ht
    have hcast : (n : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by exact_mod_cast hnm
    exact ⟨paymentTimes_min_mono_horizon (σ ω) _ _ hcast ht.1, ht.2⟩
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
      (∫⁻ ω, ⨆ n, F n ω ∂P) := by
        congr 1
        funext ω
        exact avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup
          D ω (σ ω) q T
    _ = ⨆ n, (∫⁻ ω, F n ω ∂P) := by
      exact lintegral_iSup hFmeas hFmono
    _ ≤ B := iSup_le hBound
