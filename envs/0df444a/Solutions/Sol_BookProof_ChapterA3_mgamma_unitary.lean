-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:58:34.402411+00:00
-- url     : https://prove2.me/submissions/2a0aeccd-8ce6-457f-8cbb-055fee14ad74

-- Generated from ChapterA3.lean — solution of BookProof.ChapterA3.mgamma_unitary
import Mathlib
import Definitions.Def_ChapterA3
import Theorems.Thm_BookProof_ChapterA3_mgammaZ_transpose_mul
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) :
    (mgamma μ)ᴴ * mgamma μ = 1 := by

  have hconj : (mgamma μ)ᴴ = (Int.castRingHom ℂ).mapMatrix ((mgammaZ μ)ᵀ) := by
    ext i j
    simp [mgamma, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
      Matrix.transpose_apply]
  rw [hconj, mgamma, ← map_mul, mgammaZ_transpose_mul, map_one]
