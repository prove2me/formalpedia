-- Prove2me | solution 2 for BookProof.SmBrstGhost.creat_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T10:24:59.235603+00:00
-- url     : https://prove2.me/submissions/56e6fd53-5272-417d-ae9a-a53fd6fc7f4c

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.creat_sq
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
open BookProof.SmBrstGhost

theorem solution{N : ℕ} (i : Fin N) :
    (creat i : Module.End ℂ (FermiFock N)) * creat i = 0 := by
  ext ψ S
  simp [creat]
