-- Prove2me | solution 1 for BookProof.ChapterNote68AllModes.norm_stdVec
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:57:35.759625+00:00
-- url     : https://prove2.me/submissions/1af0b590-2232-4338-a405-a90b784ec703

import Definitions.Def_ChapterNote68AllModes
open BookProof.ChapterNote68AllModes

theorem solution (i : Fin 3) : ‖stdVec i‖ = 1 := by
  simp [stdVec]

#print axioms solution
