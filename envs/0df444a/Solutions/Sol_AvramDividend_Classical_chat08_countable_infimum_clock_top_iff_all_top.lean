-- Prove2me | solution 1 for AvramDividend.Classical.chat08_countable_infimum_clock_top_iff_all_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:26:11.797104+00:00
-- url     : https://prove2.me/submissions/0c2e3498-6d2a-4d03-ada2-a5895e044034

import Mathlib.Probability.Process.Stopping

open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} (τ : ℕ → Ω → WithTop ℝ≥0) (ω : Ω) :
    (⨅ k : ℕ, τ k ω) = ⊤ ↔ ∀ k : ℕ, τ k ω = ⊤ := iInf_eq_top
