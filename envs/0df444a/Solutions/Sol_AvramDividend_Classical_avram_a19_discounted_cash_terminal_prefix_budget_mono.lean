-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_discounted_cash_terminal_prefix_budget_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:47:39.437277+00:00
-- url     : https://prove2.me/submissions/643ff437-0df7-4fbf-b9d5-dee5109576dd

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q s T : ℝ) (hst : s ≤ T) (Terminal : Ω → ℝ)
    (hFinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤)
    (hIs : Integrable (fun ω =>
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio s,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P)
    (hIT : Integrable (fun ω =>
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P)
    (hTerm : Integrable Terminal P) :
    (∫ ω, (∫⁻ t in paymentTimes (σ ω) ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Terminal ω ∂P) ≤
    (∫ ω, (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Terminal ω ∂P) := by
  have hCashAE : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio s,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
    filter_upwards [hFinite] with ω hTop
    apply ENNReal.toReal_mono hTop
    apply lintegral_mono_set
    intro t ht
    exact ⟨ht.1, lt_of_lt_of_le ht.2 hst⟩
  have hCash := integral_mono_ae hIs hIT hCashAE
  rw [integral_add hIs hTerm, integral_add hIT hTerm]
  exact add_le_add_left hCash (∫ ω, Terminal ω ∂P)
