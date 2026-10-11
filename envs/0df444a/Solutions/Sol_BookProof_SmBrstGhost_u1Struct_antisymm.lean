-- Prove2me | solution 1 for BookProof.SmBrstGhost.u1Struct_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:03:28.463039+00:00
-- url     : https://prove2.me/submissions/d36abc71-3361-4209-9306-de02462e77cd

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.u1Struct_antisymm
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section
open BookProof.SmBrstGhost

theorem solution(a b c : Fin 1) : u1Struct a b c = -u1Struct b a c := by
  simp [u1Struct]
