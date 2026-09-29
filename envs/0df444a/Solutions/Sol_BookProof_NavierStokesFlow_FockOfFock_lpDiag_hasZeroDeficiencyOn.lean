-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.lpDiag_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T09:56:32.211365+00:00
-- url     : https://prove2.me/submissions/436433f8-db4d-491f-aa25-9f1c87f539d2

-- Generated from ChapterNavierStokesFockSpace.lean — solution of BookProof.NavierStokesFlow.FockOfFock.lpDiag_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpBasis_total
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_basis
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_of_total_eigenvectors
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock









open BookProof.NavierStokesFlow.FullEsa



variable {ι : Type*}














variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (c : ι → ℝ) :
    HasZeroDeficiencyOn (lpFiniteModes ι) (lpDiag c) := by

  classical
  exact hasZeroDeficiencyOn_of_total_eigenvectors _ _ lpBasis c (lpDiag_basis c) lpBasis_total
