-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.mgamma_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:42:19.899989+00:00
-- url     : https://prove2.me/submissions/95a02628-5e50-4004-b4d4-24006a29c2de

-- Generated from ChapterMajoranaFourier.lean — solution of BookProof.ChapterMajoranaFourier.mgamma_conjTranspose
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Theorems.Thm_BookProof_ChapterMajoranaFourier_mgammaZ_transpose
import Definitions.Def_ChapterA3
open BookProof.ChapterMajoranaFourier



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) :
    (mgamma μ)ᴴ = if μ = 0 then -mgamma μ else mgamma μ := by

  have hconj : (mgamma μ)ᴴ = (Int.castRingHom ℂ).mapMatrix ((mgammaZ μ)ᵀ) := by
    ext i j
    simp [mgamma, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
      Matrix.transpose_apply]
  rw [hconj, mgammaZ_transpose]
  by_cases h : μ = 0
  · simp [h, mgamma, map_neg]
  · simp [h, mgamma]
