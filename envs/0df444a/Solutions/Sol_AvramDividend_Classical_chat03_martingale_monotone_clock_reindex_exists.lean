-- Prove2me | solution 1 for AvramDividend.Classical.chat03_martingale_monotone_clock_reindex_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:40:51.644156+00:00
-- url     : https://prove2.me/submissions/0d80b15c-ebf8-4b83-92b1-95e35a6b1745

import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-!
A monotone deterministic clock admits a sampled filtration such
that sampling any continuous-time martingale remains a martingale.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {G : Filtration ℝ≥0 mΩ}
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M G P)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) :
    ∃ H : Filtration ℕ mΩ,
      (∀ k, H k = G (clock k)) ∧
      Martingale (fun k ω => M (clock k) ω) H P := by
  refine ⟨
    ({ seq := fun k => G (clock k),
       mono' := fun _ _ h => G.mono (hc h),
       le' := fun _ => G.le _ } : Filtration ℕ mΩ),
    ?_, ?_⟩
  · intro k
    rfl
  · unfold Martingale at hM ⊢
    rcases hM with ⟨ha, hm⟩
    constructor
    · intro n
      exact ha (clock n)
    · intro i j hij
      exact hm (clock i) (clock j) (hc hij)
