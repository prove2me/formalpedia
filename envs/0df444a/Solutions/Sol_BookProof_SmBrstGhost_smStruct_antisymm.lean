-- Prove2me | solution 1 for BookProof.SmBrstGhost.smStruct_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:54:07.69943+00:00
-- url     : https://prove2.me/submissions/77239edb-29de-4f8d-8a5e-a1dc26c1c38f

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.smStruct_antisymm
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Theorems.Thm_BookProof_SmBrstGhost_sumStruct_antisymm
import Theorems.Thm_BookProof_SmBrstGhost_su2Struct_antisymm
import Theorems.Thm_BookProof_SmBrstGhost_u1Struct_antisymm
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (h3 : ∀ a b c, f3 a b c = -f3 b a c) (a b c : Fin 12) :
    smStruct f3 a b c = -smStruct f3 b a c := by

  exact sumStruct_antisymm h3
    (sumStruct_antisymm su2Struct_antisymm u1Struct_antisymm) _ _ _
