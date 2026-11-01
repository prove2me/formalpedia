-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_original_expected_full_stieltjes_reward_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:27:11.771883+00:00
-- url     : https://prove2.me/submissions/e45154ab-b424-4540-b5ce-efc4d4a73a75

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_full_stieltjes_reward_contains_initial_payment_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_complete_discounted_stieltjes_reward_finite_horizon_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

/-- The original stopped Iic reward retains the time-zero payment, while
its full expected Stieltjes mass is controlled by finite-horizon D⁺. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω : Ω, ENNReal.ofReal
        (rightLimit D (0 : ℝ≥0) ω - D (0 : ℝ≥0) ω) ∂P) ≤
      (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂(dividendMeasure D ω) ∂P) ∧
    (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω : Ω, ENNReal.ofReal (rightLimit D T ω) ∂P) := by
  have hCut (ω : Ω) :
      paymentTimes (τ ω) ∩ Iic (T : ℝ) =
        paymentTimes (τ ω) ∩ Icc (0 : ℝ) (T : ℝ) := by
    ext s
    constructor
    · intro hs
      have hs0 : (0 : ℝ) ≤ s := by
        have hp := hs.1
        change s ∈ Ici (0 : ℝ) ∩
          ({0} ∪ {t : ℝ | ENNReal.ofReal t < τ ω}) at hp
        exact hp.1
      exact ⟨hs.1, hs0, hs.2⟩
    · intro hs
      exact ⟨hs.1, hs.2.2⟩
  constructor
  · apply lintegral_mono
    intro ω
    change ENNReal.ofReal
        (rightLimit D (0 : ℝ≥0) ω - D (0 : ℝ≥0) ω) ≤
      (∫⁻ s in paymentTimes (τ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω)
    rw [hCut ω]
    exact avram_wave4_04b_stopped_full_stieltjes_reward_contains_initial_payment_atom
      D hD ω T (τ ω) q
  · apply lintegral_mono
    intro ω
    change (∫⁻ s in paymentTimes (τ ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) ≤
        ENNReal.ofReal (rightLimit D T ω)
    rw [hCut ω]
    exact avram_wave4_04b_complete_discounted_stieltjes_reward_finite_horizon_budget
      D hD ω T (τ ω) q hq
