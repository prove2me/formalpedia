-- Prove2me | solution 1 for BookProof.SmBrstGhost.ghostMode_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:49:15.171988+00:00
-- url     : https://prove2.me/submissions/4d773767-8c84-46ac-b442-5b6b057fdbb8

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.ghostMode_injective
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
open BookProof.SmBrstGhost

theorem solution(m : ℕ) : Function.Injective (ghostMode m) := by
  intro a b h
  have h2 := congrArg Fin.val h
  simp only [ghostMode, Fin.coe_natAdd] at h2
  exact Fin.ext (by omega)
