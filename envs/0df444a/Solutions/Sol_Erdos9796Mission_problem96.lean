-- Prove2me | solution 1 for Erdos9796Mission.problem96
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T07:01:32.602904+00:00
-- url     : https://prove2.me/submissions/ea6648ee-430d-44f6-b705-8267653163a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Erdos9796Mission
import Theorems.Thm_Erdos9796Mission_linear_bound_of_problem97
import Theorems.Thm_Erdos9796Mission_problem97

open Erdos9796Mission

/-- The proved bridge gives both the pointwise `3|A|` estimate and Problem 96 from a proof
of Problem 97. This reduction selects its Problem 96 component, recording the intended
dependency edge from the second Erdős problem to the first and to the bridge theorem. -/
theorem solution : Erdos9796Mission.Problem96 :=
  (linear_bound_of_problem97 problem97).2

