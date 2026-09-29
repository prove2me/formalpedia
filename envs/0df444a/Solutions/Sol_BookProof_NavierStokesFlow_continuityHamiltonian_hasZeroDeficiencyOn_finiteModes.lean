-- Prove2me | solution 1 for BookProof.NavierStokesFlow.continuityHamiltonian_hasZeroDeficiencyOn_finiteModes
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T03:22:07.984883+00:00
-- url     : https://prove2.me/submissions/5a4cea38-141b-451a-a445-4a7a1b57a15b

import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesEsa.lean — solution of BookProof.NavierStokesFlow.continuityHamiltonian_hasZeroDeficiencyOn_finiteModes
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
import Theorems.Thm_BookProof_NavierStokesFlow_continuityHamiltonian_mem_finiteModes
import Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_of_bounded_symmetric
import Definitions.Def_ChapterDirectSumEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution (v : LinfZ) :
    HasZeroDeficiencyOn finiteModes
      (LinearMap.codRestrict finiteModes
        ((continuityHamiltonian v : L2Z →ₗ[ℂ] L2Z).comp finiteModes.subtype)
        fun f => continuityHamiltonian_mem_finiteModes v f.2) :=
  hasZeroDeficiencyOn_of_bounded_symmetric (continuityHamiltonian v)
      (continuityHamiltonian_isSymmetric v) finiteModes finiteModes_dense
      fun f => continuityHamiltonian_mem_finiteModes v f.2