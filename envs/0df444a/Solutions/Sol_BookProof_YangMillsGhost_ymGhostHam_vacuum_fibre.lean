-- Prove2me | solution 1 for BookProof.YangMillsGhost.ymGhostHam_vacuum_fibre
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:25.062195+00:00
-- url     : https://prove2.me/submissions/89130dd9-4a86-499d-8799-1fae9d0ea368

-- Generated from ChapterYangMillsGhostSector.lean — solution of BookProof.YangMillsGhost.ymGhostHam_vacuum_fibre
import Mathlib
import Definitions.Def_ChapterYangMillsGhostSector
import Theorems.Thm_BookProof_YangMillsGhost_ghostEnergy_empty
import Theorems.Thm_BookProof_YangMillsGhost_fibreHam_apply
import Theorems.Thm_BookProof_YangMillsGhost_ymGhostHam_fibre
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.YangMillsGhost















noncomputable section

open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.YangMillsHermite
open BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent

variable {K : ℕ}

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
-- the direct-sum coercions of `lp` over the ghost configurations make the defeq checks here
-- expensive
theorem solution (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (ω : Fin K → ℝ)
    (x : ghostCore K) :
    ((ymGhostHam fabc ω x : GhostSpace K) : ∀ _ : GConf K, L2d 99) ∅
      = ymHamiltonian (coreRepPoly 99) fabc ⟨(x : GhostSpace K) ∅, x.2.2 ∅⟩ := by

  rw [ymGhostHam_fibre, fibreHam_apply, ghostEnergy_empty]
  simp
