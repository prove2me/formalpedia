-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_same_side_shrinking_increments_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:35:57.881672+00:00
-- url     : https://prove2.me/submissions/bbc89352-a608-4d6e-91c2-5eb3af863990

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- The two same-side possibilities in a shrinking cadlag grid cell each
have zero limiting increment. The crossing case recovers the true jump. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℕ → ℝ≥0)
    (hL : Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ContinuousWithinAt Y (Ici t) t) :
    ((Tendsto a atTop (𝓝[<] t) ∧ Tendsto b atTop (𝓝[<] t)) →
      Tendsto (fun n => Y (b n) - Y (a n)) atTop (𝓝 (0 : ℝ))) ∧
    ((Tendsto a atTop (nhdsWithin t (Ici t)) ∧
      Tendsto b atTop (nhdsWithin t (Ici t))) →
      Tendsto (fun n => Y (b n) - Y (a n)) atTop (𝓝 (0 : ℝ))) := by
  constructor
  · rintro ⟨ha, hb⟩
    simpa [Function.comp_def] using (hL.comp hb).sub (hL.comp ha)
  · rintro ⟨ha, hb⟩
    simpa [Function.comp_def] using
      (hR.tendsto.comp hb).sub (hR.tendsto.comp ha)
