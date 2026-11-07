-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_hjb_exit_budget_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:18:42.124411+00:00
-- url     : https://prove2.me/submissions/8e4fe51e-e40c-4e5c-92bf-c79b030ac86b

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ≥0∞)
    (hf : ∀ n : ℕ, Measurable (f n)) (hmono : Monotone f)
    (a c : ℝ≥0∞)
    (hbudget : ∀ n : ℕ, a * (∫⁻ ω, f n ω ∂P) ≤ c) :
    a * (∫⁻ ω, (⨆ n : ℕ, f n ω) ∂P) ≤ c := by
  rw [MeasureTheory.lintegral_iSup hf hmono, ENNReal.mul_iSup]
  exact iSup_le fun n => hbudget n
