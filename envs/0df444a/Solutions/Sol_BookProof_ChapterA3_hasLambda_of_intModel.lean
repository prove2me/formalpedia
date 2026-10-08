-- Prove2me | solution 1 for BookProof.ChapterA3.hasLambda_of_intModel
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:53:40.624624+00:00
-- url     : https://prove2.me/submissions/af1cd0be-9925-487b-969b-81c68ec69370

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix
set_option autoImplicit false
set_option maxHeartbeats 0

theorem solution (Sz Λz : Matrix (Fin 4) (Fin 4) ℤ)
    (hSS : Sz * Sz = -1)
    (hconj : ∀ μ, -Sz * mgammaZ μ * Sz = ∑ ν, Λz μ ν • mgammaZ ν) :
    HasLambda ((Int.castRingHom ℝ).mapMatrix Sz)
      ((Int.castRingHom ℝ).mapMatrix Λz) := by
  let S := (Int.castRingHom ℝ).mapMatrix Sz
  have hs : S * S = -1 := by
    have hh := congrArg ((Int.castRingHom ℝ).mapMatrix) hSS
    rw [map_mul, map_neg, map_one] at hh
    exact hh
  have hi : S⁻¹ = -S := by
    apply Matrix.inv_eq_left_inv
    rw [neg_mul, hs, neg_neg]
  intro μ
  change S⁻¹ * mgammaR μ * S = _
  rw [hi]
  change -S * mgammaR μ * S = ∑ ν, (Λz μ ν : ℝ) • mgammaR ν
  have hh := congrArg ((Int.castRingHom ℝ).mapMatrix) (hconj μ)
  simp only [map_mul, map_neg, map_sum, map_zsmul] at hh
  simpa only [S, mgammaR, Int.cast_smul_eq_zsmul] using hh

#print axioms solution
