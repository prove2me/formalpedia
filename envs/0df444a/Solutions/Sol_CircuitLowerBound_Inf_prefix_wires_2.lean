-- Prove2me | solution 2 for CircuitLowerBound.Inf.prefix_wires
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:08:43.087509+00:00
-- url     : https://prove2.me/submissions/4ea94724-7377-4342-abc2-42c958a1b59c

import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf

set_option autoImplicit false

open CircuitLowerBound CircuitLowerBound.Inf
open ENP

private theorem wires_concat (x : List Bool) (C : Circuit) (G : Gate) :
    wires x (C ++ [G]) =
      wires x C ++ [G.op ((wires x C).getD G.in₁ false) ((wires x C).getD G.in₂ false)] := by
  simp [wires]

theorem solution (x : List Bool) (C : Circuit) : x <+: wires x C := by
  induction C using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton C G ih =>
    rw [wires_concat]
    exact ih.trans (List.prefix_append _ _)
