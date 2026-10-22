-- Prove2me | solution 1 for AvramDividend.Classical.chat03_monotone_clock_reindexed_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T05:36:45.586262+00:00
-- url     : https://prove2.me/submissions/b304cda3-2556-4a07-a38f-0ad7da91c9f4

import Mathlib.Probability.Process.Filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

/-!
Pull back a continuous-time filtration along an arbitrary monotone
discrete sampling clock. The sampled sigma-algebras form a genuine
discrete filtration without additional stochastic assumptions.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) :
    ∃ H : Filtration ℕ mΩ, ∀ k, H k = 𝓕 (clock k) := by
  refine ⟨{
    seq := fun k => 𝓕 (clock k)
    mono' := ?_
    le' := ?_
  }, ?_⟩
  · intro i j hij
    exact 𝓕.mono (hc hij)
  · intro i
    exact 𝓕.le (clock i)
  · intro i
    rfl
