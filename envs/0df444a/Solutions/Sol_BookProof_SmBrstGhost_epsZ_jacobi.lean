-- Prove2me | solution 1 for BookProof.SmBrstGhost.epsZ_jacobi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:54:03.336817+00:00
-- url     : https://prove2.me/submissions/8cc11f55-06a4-4d8d-855d-e8cde6ce8618

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.epsZ_jacobi
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : ∀ a b c h : Fin 3,
    ∑ e, (epsZ a b e * epsZ e c h + epsZ b c e * epsZ e a h + epsZ c a e * epsZ e b h) = 0 := by

  decide
