-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_crossing_large_increments_force_large_actual_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:28:20.824056+00:00
-- url     : https://prove2.me/submissions/a724110d-c9c7-4c9c-87ec-84d2dea752cd

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_shrinking_cell_increment_converges_to_actual_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- A uniformly large increment on cells straddling a common time forces
the corresponding genuine cadlag jump to be at least as large. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℕ → ℝ≥0)
    (ha : Tendsto a atTop (𝓝[<] t))
    (hb : Tendsto b atTop (nhdsWithin t (Ici t)))
    (hL : Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ)
    (hlarge : ∀ n : ℕ, ρ ≤ |Y (b n) - Y (a n)|) :
    ρ ≤ |Y t - Function.leftLim Y t| := by
  have hinc :=
    avram_p2_34dbea70_shrinking_cell_increment_converges_to_actual_jump
      Y t a b ha hb hL hR
  exact ge_of_tendsto hinc.abs (Filter.Eventually.of_forall hlarge)
