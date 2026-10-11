-- Prove2me | solution 1 for BookProof.SmBrstGhost.epsZ_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:54:01.789016+00:00
-- url     : https://prove2.me/submissions/4015443b-0b3a-4f8f-bb3a-dc286603fb19

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.epsZ_antisymm
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section
open BookProof.SmBrstGhost

theorem solution: ∀ a b c : Fin 3, epsZ a b c = -epsZ b a c := by
  first
  | decide
  | (intro a b c; fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [epsZ] <;> decide)
  | (intro a b c; fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl)
