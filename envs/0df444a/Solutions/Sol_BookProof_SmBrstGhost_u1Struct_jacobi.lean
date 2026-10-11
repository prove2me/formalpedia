-- Prove2me | solution 1 for BookProof.SmBrstGhost.u1Struct_jacobi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:54:06.644081+00:00
-- url     : https://prove2.me/submissions/3f4cb93b-8d7f-4b58-8da9-d28ae3e6891f

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.u1Struct_jacobi
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (a b c h : Fin 1) :
    ∑ e, (u1Struct a b e * u1Struct e c h + u1Struct b c e * u1Struct e a h
      + u1Struct c a e * u1Struct e b h) = 0 := by

  simp [u1Struct]
