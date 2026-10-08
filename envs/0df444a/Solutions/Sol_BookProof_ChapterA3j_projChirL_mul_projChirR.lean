-- Prove2me | solution 1 for BookProof.ChapterA3j.projChirL_mul_projChirR
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T15:30:48.902281+00:00
-- url     : https://prove2.me/submissions/e5bad4f0-5153-4adc-a169-7acb6ed6ecaf

import Mathlib
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3

open Matrix
open BookProof.ChapterA3
open BookProof.ChapterA3j

private theorem chir_sq_local : chir * chir = -1 := by
  have hz : BookProof.ChapterA3.mgamma5Z *
      BookProof.ChapterA3.mgamma5Z = -1 := by
    decide
  change ((Int.castRingHom ℂ).mapMatrix BookProof.ChapterA3.mgamma5Z) *
      ((Int.castRingHom ℂ).mapMatrix BookProof.ChapterA3.mgamma5Z) = -1
  rw [← map_mul, hz]
  ext i j
  simp [Matrix.one_apply]

private theorem i_chir_sq_local :
    (Complex.I • chir) * (Complex.I • chir) = 1 := by
  calc
    (Complex.I • chir) * (Complex.I • chir) =
        Complex.I • (Complex.I • (chir * chir)) := by
      rw [smul_mul_assoc, mul_smul_comm]
    _ = (Complex.I * Complex.I) • (chir * chir) := by
      rw [smul_smul]
    _ = 1 := by
      have hI : Complex.I * Complex.I = -1 := by norm_num [Complex.I_sq]
      rw [hI, chir_sq_local]
      simp

theorem solution : projChirL * projChirR = 0 := by
  have hzero :
      (1 - Complex.I • chir) * (1 + Complex.I • chir) = 0 := by
    have hu := i_chir_sq_local
    simp only [sub_mul, mul_add, one_mul, mul_one, hu]
    abel
  let a : ℂ := (2 : ℂ)⁻¹
  let x : Matrix (Fin 4) (Fin 4) ℂ := 1 - Complex.I • chir
  let y : Matrix (Fin 4) (Fin 4) ℂ := 1 + Complex.I • chir
  change (a • x) * (a • y) = 0
  calc
    (a • x) * (a • y) = (a * a) • (x * y) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = (a * a) • 0 := by
      simpa [x, y] using congrArg (fun z : Matrix (Fin 4) (Fin 4) ℂ => (a * a) • z) hzero
    _ = 0 := by simp

#print axioms solution
