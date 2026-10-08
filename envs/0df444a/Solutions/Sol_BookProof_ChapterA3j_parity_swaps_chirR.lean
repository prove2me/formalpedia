-- Prove2me | solution 1 for BookProof.ChapterA3j.parity_swaps_chirR
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:12:56.780773+00:00
-- url     : https://prove2.me/submissions/641d8771-30f4-4ac1-9c06-ced0d3c17cda

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

private theorem chir_parity_numerator_right_local :
    (1 + Complex.I • chir) * mgamma 0 =
      mgamma 0 * (1 - Complex.I • chir) := by
  calc
    (1 + Complex.I • chir) * mgamma 0 =
        mgamma 0 + (Complex.I • chir) * mgamma 0 := by
      simp only [add_mul, one_mul]
    _ = mgamma 0 - mgamma 0 * (Complex.I • chir) := by
      rw [scaled_chir_parity_anticomm_local]
      abel
    _ = mgamma 0 * (1 - Complex.I • chir) := by
      rw [mul_sub, mul_one]

theorem solution : projChirR * mgamma 0 = mgamma 0 * projChirL := by
  let a : ℂ := (2 : ℂ)⁻¹
  let u : Matrix (Fin 4) (Fin 4) ℂ := Complex.I • chir
  have hnum : (1 + u) * mgamma 0 = mgamma 0 * (1 - u) := by
    simpa [u] using chir_parity_numerator_right_local
  change (a • (1 + u)) * mgamma 0 = mgamma 0 * (a • (1 - u))
  calc
    (a • (1 + u)) * mgamma 0 = a • ((1 + u) * mgamma 0) := by
      rw [smul_mul_assoc]
    _ = a • (mgamma 0 * (1 - u)) := by rw [hnum]
    _ = mgamma 0 * (a • (1 - u)) := by rw [← mul_smul_comm]

#print axioms solution
