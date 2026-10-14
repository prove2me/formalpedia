-- Prove2me | solution 2 for BookProof.SmBrstGhost.annih_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T10:24:51.404401+00:00
-- url     : https://prove2.me/submissions/106a0ea4-b06b-4fd1-93b0-7b6765cae2aa

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.annih_sq
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
    (annih i : Module.End ℂ (FermiFock N)) * annih i = 0 := by
  ext ψ S
  simp [annih]
