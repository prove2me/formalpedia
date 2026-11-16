-- Prove2me | solution 1 for FixedKMachine.branch_machine
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:02:58.947438+00:00
-- url     : https://prove2.me/submissions/5e8bcb34-752d-4c59-a291-36f925f12901

import Mathlib
open MeasureTheory Set

theorem solution (H F I N : Prop)
    (hcases : ¬H → F ∨ I) (hRH : H → ¬N)
    (hfinite : N → ¬F) (hinfinite : N → ¬I) : ¬N := by
  intro hN
  by_cases hH : H
  · exact hRH hH hN
  · rcases hcases hH with hF | hI
    · exact hfinite hN hF
    · exact hinfinite hN hI
