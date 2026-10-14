-- Prove2me | solution 1 for BookProof.SmBrstGhost.ghostNumber_occ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:55:31.537377+00:00
-- url     : https://prove2.me/submissions/49d06561-c146-4331-ac2f-99f03b94d2b0

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.ghostNumber_occ
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Theorems.Thm_BookProof_SmBrstGhost_occupation_occ
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterNavierStokes
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (m : ℕ) (S : Finset (Fin (m + 12))) :
    ghostNumber m (occ S)
      = (Finset.univ.filter (fun a : Fin 12 => ghostMode m a ∈ S)).card • occ S := by

  classical
  rw [ghostNumber, LinearMap.sum_apply]
  have hterm : ∀ a : Fin 12, (ghostCre m a * ghostAnn m a) (occ S)
      = if ghostMode m a ∈ S then occ S else 0 := fun a => occupation_occ (ghostMode m a) S
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hterm a]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]
