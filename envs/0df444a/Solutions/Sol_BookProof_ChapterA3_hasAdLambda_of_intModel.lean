-- Prove2me | solution 1 for BookProof.ChapterA3.hasAdLambda_of_intModel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:03:45.987843+00:00
-- url     : https://prove2.me/submissions/f4ea9d9f-0b5e-4f05-a32a-5253d696ac87

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.hasAdLambda_of_intModel
import Mathlib
import Definitions.Def_ChapterA3e
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (Gz Az : Matrix (Fin 4) (Fin 4) ℤ)
    (hconj : ∀ μ, Gz * mgammaZ μ - mgammaZ μ * Gz = ∑ ν, Az μ ν • mgammaZ ν) :
    HasAdLambda ((Int.castRingHom ℝ).mapMatrix Gz)
      ((Int.castRingHom ℝ).mapMatrix Az) := by

  intro μ
  have hmg : mgammaR μ = (Int.castRingHom ℝ).mapMatrix (mgammaZ μ) := rfl
  have hL : (Int.castRingHom ℝ).mapMatrix Gz * mgammaR μ
      - mgammaR μ * (Int.castRingHom ℝ).mapMatrix Gz
      = (Int.castRingHom ℝ).mapMatrix (Gz * mgammaZ μ - mgammaZ μ * Gz) := by
    rw [hmg]; simp only [map_sub, map_mul]
  rw [hL, hconj μ, map_sum]
  apply Finset.sum_congr rfl
  intro ν _
  have hcast : ((Int.castRingHom ℝ).mapMatrix Az) μ ν = ((Az μ ν : ℤ) : ℝ) := by
    simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [hcast, map_zsmul, Int.cast_smul_eq_zsmul]
  rfl
