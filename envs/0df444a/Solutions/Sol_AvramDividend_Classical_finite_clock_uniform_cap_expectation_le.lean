-- Prove2me | solution 1 for AvramDividend.Classical.finite_clock_uniform_cap_expectation_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:50:10.774561+00:00
-- url     : https://prove2.me/submissions/aeb8892e-1771-4c09-b475-8043a7ac934f

import Theorems.Thm_AvramDividend_Classical_finite_clock_reward_lintegral_eq_sup_caps
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (clock : Ω → ℝ≥0∞) (reward : Ω → ℝ≥0∞)
    (hclock : Measurable clock) (hreward : Measurable reward)
    (bound : ℝ≥0∞)
    (hcap : ∀ n : ℕ,
      (∫⁻ ω, if clock ω ≤ (n : ℝ≥0∞) then reward ω else 0 ∂P) ≤ bound) :
    (∫⁻ ω, if clock ω < ⊤ then reward ω else 0 ∂P) ≤ bound := by
  rw [finite_clock_reward_lintegral_eq_sup_caps P clock reward hclock hreward]
  exact iSup_le hcap
