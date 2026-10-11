-- Prove2me | solution 1 for BookProof.NavierStokesEulerian.nsBrst_not_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:32.611545+00:00
-- url     : https://prove2.me/submissions/c3d4d847-217f-466b-a940-0e1075b4813e

-- Generated from ChapterNavierStokesEulerian.lean — solution of BookProof.NavierStokesEulerian.nsBrst_not_hermitian
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Theorems.Thm_BookProof_NavierStokesFlow_nsBrst_adjoint
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesEulerian




open BookProof.NavierStokesFlow Matrix
open BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (d : NSTruncation n) (h : nsDivergence d ≠ 0) :
    (nsBrstCharge d)ᴴ ≠ nsBrstCharge d := by

  intro hEq
  apply h
  ext a b
  have := congrFun (congrFun hEq (a, 0)) (b, 1)
  rw [nsBrst_adjoint] at this
  simpa [nsBrstCharge, Matrix.kroneckerMap_apply, BookProof.GhostField.psi,
    BookProof.GhostField.psiDag] using this.symm
