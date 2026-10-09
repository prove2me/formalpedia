-- Prove2me | solution 1 for BookProof.ChapterA3.lorentzLie_of_intModel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:05:04.93704+00:00
-- url     : https://prove2.me/submissions/a4593095-5d85-494d-8283-6091966bdaa3

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.lorentzLie_of_intModel
import Mathlib
import Definitions.Def_ChapterA3e
import Theorems.Thm_BookProof_ChapterA3_castMat_minkowskiMatZ
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (Az : Matrix (Fin 4) (Fin 4) ℤ)
    (h : Az * minkowskiMatZ + minkowskiMatZ * Azᵀ = 0) :
    (Int.castRingHom ℝ).mapMatrix Az ∈ LorentzLie := by

  have hc := congrArg (Int.castRingHom ℝ).mapMatrix h
  rw [map_add, map_mul, map_mul, map_zero] at hc
  have ht : (Int.castRingHom ℝ).mapMatrix (Azᵀ)
      = ((Int.castRingHom ℝ).mapMatrix Az)ᵀ := by
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]
  rw [ht, castMat_minkowskiMatZ] at hc
  exact hc
