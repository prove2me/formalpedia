-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin29_original_bounded_stop_kernel_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:41:06.709179+00:00
-- url     : https://prove2.me/submissions/98cfce0b-6631-4944-b996-31953538a0a0

import Mathlib.Algebra.Notation.Indicator
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*}
    (T : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ T)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : S = {p | p.1.1 ≤ T})
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p => if p.1.1 ≤ ρ p.1.2 then G p else 0) :
    S.indicator H = H := by
  rw [hS, hH]
  funext p
  by_cases ht : p.1.1 ≤ T
  · simp [Set.indicator_of_mem, ht]
  · have hnot : ¬ p.1.1 ≤ ρ p.1.2 := by
      intro hle
      exact ht (hle.trans (hρbound p.1.2))
    simp [Set.indicator_of_notMem, ht, hnot]
