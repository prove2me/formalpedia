-- Prove2me | solution 2 for BookProof.SmBrstGhost.su2Struct_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:54:04.344632+00:00
-- url     : https://prove2.me/submissions/0f941c98-7c45-4dfc-8c03-e26523500652

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.su2Struct_antisymm
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Theorems.Thm_BookProof_SmBrstGhost_epsZ_antisymm
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (a b c : Fin 3) : su2Struct a b c = -su2Struct b a c := by

  rw [su2Struct, su2Struct, epsZ_antisymm a b c]
  push_cast
  ring
