-- Prove2me | solution 1 for ConsistentSubmodular.minimax
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:50.462604+00:00
-- url     : https://prove2.me/submissions/183dcdff-ada7-47e1-846d-8d87ff05e68a

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_Minimax_minimax

section

open ConsistentSubmodular

theorem solution : MinimaxGoal :=
  Minimax.minimax

end
