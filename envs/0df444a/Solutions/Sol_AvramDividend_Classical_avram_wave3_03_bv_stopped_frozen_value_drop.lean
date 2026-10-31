-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_stopped_frozen_value_drop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:50:36.10921+00:00
-- url     : https://prove2.me/submissions/6af9db42-e0b0-48dd-9703-768008ec9c8c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_frozen_reserve_closed_discounted_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The true stopped discounted Stieltjes payout, including its continuous
part, is dominated by the frozen-reserve HJB value drop. The stopped payment
set may exclude the terminal atom, but the upper bound includes it. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (C : ℝ≥0∞) (hC : 0 < C) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0) (y : ℝ)
    (hyD : rightLimit D T ω ≤ y) (hyC : ENNReal.ofReal y ≤ C) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (w y - w (y - rightLimit D T ω)) := by
  have hsubset : paymentTimes σ ∩ Iic (T : ℝ) ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro t ht
    exact ⟨ht.1.1, ht.2⟩
  calc
    _ ≤ (∫⁻ t in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
        lintegral_mono_set hsubset
    _ ≤ _ := avram_wave3_03_bv_frozen_reserve_closed_discounted_budget
      C hC q hq w hw_cont hw_smooth hw_grad D hD ω T y hyD hyC
