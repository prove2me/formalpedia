-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys86_max_positive_error_two_step_composition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:08:17.034621+00:00
-- url     : https://prove2.me/submissions/8a685295-1294-474a-9aed-90bbaf6d1890

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped Topology
noncomputable section

/-- Two vanishing positive errors compose through an intermediate frozen
drift grid, yielding the generator-compensated cash inequality. -/
theorem solution (F G K L : ℕ → ℝ) (w : ℝ)
    (hCash : Tendsto (fun n => max (F n - (w + L n)) 0)
      atTop (𝓝 (0 : ℝ)))
    (hComp : Tendsto (fun n => max (L n - (G n - K n)) 0)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => max (F n - (w + (-K n + G n))) 0)
      atTop (𝓝 (0 : ℝ)) := by
  have hsum : Tendsto
      (fun n => max (F n - (w + L n)) 0 +
        max (L n - (G n - K n)) 0) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_add] using hCash.add hComp
  have hlow : ∀ n : ℕ, (0 : ℝ) ≤
      max (F n - (w + (-K n + G n))) 0 := by
    intro n
    exact le_max_right _ _
  have hhigh : ∀ n : ℕ,
      max (F n - (w + (-K n + G n))) 0 ≤
      max (F n - (w + L n)) 0 +
      max (L n - (G n - K n)) 0 := by
    intro n
    have hsplit : F n - (w + (-K n + G n)) =
        (F n - (w + L n)) + (L n - (G n - K n)) := by ring
    rw [hsplit]
    apply max_le
    · linarith [le_max_left (F n - (w + L n)) (0 : ℝ),
        le_max_left (L n - (G n - K n)) (0 : ℝ)]
    · linarith [le_max_right (F n - (w + L n)) (0 : ℝ),
        le_max_right (L n - (G n - K n)) (0 : ℝ)]
  exact Filter.Tendsto.squeeze' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall hlow)
    (Filter.Eventually.of_forall hhigh)
