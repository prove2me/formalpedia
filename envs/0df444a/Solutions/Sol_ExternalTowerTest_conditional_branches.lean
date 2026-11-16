-- Prove2me | solution 1 for ExternalTowerTest.conditional_branches
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:33:42.902198+00:00
-- url     : https://prove2.me/submissions/495c485c-19a3-4daa-bace-9af96a6edbde

import Mathlib
open Filter Topology

theorem solution (Negative FiniteOff InfiniteOff RH : Prop)
    (cases : ¬ RH → FiniteOff ∨ InfiniteOff)
    (branch2 : Negative → ¬ FiniteOff)
    (branch3 : Negative → ¬ InfiniteOff)
    (rh_sign : RH → ¬ Negative) : ¬ Negative := by
  intro hn
  have hr : RH := by
    by_contra h
    rcases cases h with hf | hi
    · exact branch2 hn hf
    · exact branch3 hn hi
  exact rh_sign hr hn

-- A single verified negative value is not a proof of an arithmetic branch.
