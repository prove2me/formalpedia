-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_candidate_uniform_continuity_on_reserves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:41:22.061725+00:00
-- url     : https://prove2.me/submissions/66986824-0f53-4140-b287-42e13a825682

import Mathlib
open Set

theorem solution
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Ici 0)) :
    UniformContinuousOn w (Icc 0 b)  := by
  have hcont : ContinuousOn w (Icc 0 b) :=
    hw_cont.mono (fun z hz => hz.1)
  exact isCompact_Icc.uniformContinuousOn_of_continuous hcont
