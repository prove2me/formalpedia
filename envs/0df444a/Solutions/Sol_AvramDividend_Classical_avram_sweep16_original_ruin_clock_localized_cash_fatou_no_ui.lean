-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_ruin_clock_localized_cash_fatou_no_ui
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:08:16.071938+00:00
-- url     : https://prove2.me/submissions/7442bf5d-0e0e-42a9-a4c5-c71121fb347d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (LocalCash : ℕ → Ω → ℝ≥0∞)
    (hLocalMeas : ∀ k, Measurable (LocalCash k))
    (hLocalBudget : ∀ k,
      (∫⁻ ω, LocalCash k ω ∂P) ≤ ENNReal.ofReal (w x))
    (hCashLiminf : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      Filter.liminf (fun k : ℕ => LocalCash k ω) Filter.atTop) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  calc
    _ ≤ (∫⁻ ω, Filter.liminf (fun k : ℕ => LocalCash k ω) Filter.atTop ∂P) :=
      lintegral_mono_ae hCashLiminf
    _ ≤ Filter.liminf (fun k : ℕ => ∫⁻ ω, LocalCash k ω ∂P) Filter.atTop :=
      lintegral_liminf_le hLocalMeas
    _ ≤ ENNReal.ofReal (w x) := by
      apply Filter.liminf_le_of_le
      · refine ⟨0, ?_⟩
        exact Filter.Eventually.of_forall (fun _ => bot_le)
      · intro b hb
        obtain ⟨k, hk⟩ := hb.exists
        exact hk.trans (hLocalBudget k)
