-- Prove2me | solution 1 for BookProof.YangMillsGhost.fibreHam_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:23.404653+00:00
-- url     : https://prove2.me/submissions/b14c987c-3e71-4964-84d0-af261aef5ae3

-- Generated from ChapterYangMillsGhostSector.lean — solution of BookProof.YangMillsGhost.fibreHam_symmetricOn
import Mathlib
import Definitions.Def_ChapterYangMillsGhostSector
import Theorems.Thm_BookProof_YangMillsGhost_fibreHam_apply
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_symmetricOn
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
-- the `L²` coercions of the Gauss–polynomial core make the defeq checks here expensive
theorem solution (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (ω : Fin K → ℝ)
    (S : GConf K) : SymmetricOn (polyGaussCore (d := 99)) (fibreHam fabc ω S) := by

  intro x y
  have hsym := ymHamiltonian_symmetricOn (coreRepPoly 99) fabc x y
  rw [fibreHam_apply, fibreHam_apply, inner_add_left, inner_add_right, hsym,
    inner_smul_left, inner_smul_right]
  simp
