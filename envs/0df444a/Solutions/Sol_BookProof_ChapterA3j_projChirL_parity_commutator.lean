-- Prove2me | solution 1 for BookProof.ChapterA3j.projChirL_parity_commutator
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:14:42.346922+00:00
-- url     : https://prove2.me/submissions/1a26123e-52ef-4d31-bb8f-9f982f2149a9

import Mathlib
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3

open Matrix
open BookProof.ChapterA3
open BookProof.ChapterA3j

private theorem chir_parity_anticomm_local :
    chir * mgamma 0 = -(mgamma 0 * chir) := by
  have hz : mgamma5Z * mgammaZ 0 = -(mgammaZ 0 * mgamma5Z) := by
    decide
  change ((Int.castRingHom ℂ).mapMatrix mgamma5Z) *
      ((Int.castRingHom ℂ).mapMatrix (mgammaZ 0)) =
        -(((Int.castRingHom ℂ).mapMatrix (mgammaZ 0)) *
          ((Int.castRingHom ℂ).mapMatrix mgamma5Z))
  simpa only [map_mul, map_neg] using
    congrArg ((Int.castRingHom ℂ).mapMatrix) hz

private theorem scaled_chir_parity_anticomm_local :
    (Complex.I • chir) * mgamma 0 = -(mgamma 0 * (Complex.I • chir)) := by
  calc
    (Complex.I • chir) * mgamma 0 = Complex.I • (chir * mgamma 0) := by
      rw [smul_mul_assoc]
    _ = Complex.I • (-(mgamma 0 * chir)) := by
      rw [chir_parity_anticomm_local]
    _ = -(Complex.I • (mgamma 0 * chir)) := by simp
    _ = -(mgamma 0 * (Complex.I • chir)) := by
      rw [← mul_smul_comm]

theorem solution :
    projChirL * mgamma 0 - mgamma 0 * projChirL =
      Complex.I • (mgamma 0 * chir) := by
  let a : ℂ := (2 : ℂ)⁻¹
  let u : Matrix (Fin 4) (Fin 4) ℂ := Complex.I • chir
  let g : Matrix (Fin 4) (Fin 4) ℂ := mgamma 0
  have hanti : u * g = -(g * u) := by
    dsimp [u, g]
    exact scaled_chir_parity_anticomm_local
  have hnum : (1 - u) * g = g * (1 + u) := by
    calc
      (1 - u) * g = g - u * g := by rw [sub_mul, one_mul]
      _ = g + g * u := by rw [hanti]; abel
      _ = g * (1 + u) := by rw [mul_add, mul_one]
  have hswap : (a • (1 - u)) * g = g * (a • (1 + u)) := by
    calc
      (a • (1 - u)) * g = a • ((1 - u) * g) := by
        rw [smul_mul_assoc]
      _ = a • (g * (1 + u)) := by rw [hnum]
      _ = g * (a • (1 + u)) := by rw [← mul_smul_comm]
  have ha : a * (2 : ℂ) = 1 := by
    dsimp [a]
    norm_num
  have hinner : (1 + u) - (1 - u) = (2 : ℂ) • u := by
    calc
      (1 + u) - (1 - u) = u + u := by abel
      _ = (2 : ℂ) • u := by rw [two_smul]
  have hdiff : a • (1 + u) - a • (1 - u) = u := by
    rw [← smul_sub]
    rw [hinner, smul_smul, ha]
    simp
  change (a • (1 - u)) * g - g * (a • (1 - u)) =
    Complex.I • (g * chir)
  calc
    (a • (1 - u)) * g - g * (a • (1 - u)) =
        g * (a • (1 + u)) - g * (a • (1 - u)) := by rw [hswap]
    _ = g * (a • (1 + u) - a • (1 - u)) := by rw [mul_sub]
    _ = g * u := by rw [hdiff]
    _ = Complex.I • (g * chir) := by
      dsimp [u]
      rw [mul_smul_comm]

#print axioms solution
