-- Prove2me | solution 1 for BookProof.NavierStokesEulerian.nsBrst_symmetrization_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:33.953372+00:00
-- url     : https://prove2.me/submissions/e544c2ac-9721-4f8e-9fc2-7c2d2926ffc1

-- Generated from ChapterNavierStokesEulerian.lean — solution of BookProof.NavierStokesEulerian.nsBrst_symmetrization_hermitian
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesEulerian




open BookProof.NavierStokesFlow Matrix

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (d : NSTruncation n) :
    (nsBrstCharge d + (nsBrstCharge d)ᴴ)ᴴ = nsBrstCharge d + (nsBrstCharge d)ᴴ := by

  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
