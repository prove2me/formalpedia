-- Prove2me | solution 1 for BookProof.SmBrstGhost.su2Struct_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:53:44.669238+00:00
-- url     : https://prove2.me/submissions/1bcfe1ef-f708-47b9-aad0-d968f9a56c06

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.su2Struct_antisymm
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section
open BookProof.SmBrstGhost

theorem solution(a b c : Fin 3) : su2Struct a b c = -su2Struct b a c := by
  unfold su2Struct
  have h : epsZ a b c = -epsZ b a c := by
    revert a b c
    decide
  rw [h]
  push_cast
  ring
