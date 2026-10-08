-- Prove2me | solution 1 for BookProof.ChapterA3j.projChirL_idem
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T15:30:20.656382+00:00
-- url     : https://prove2.me/submissions/ecd8501a-20b1-4c3c-a596-35782e3323bb

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

theorem solution : projChirL * projChirL = projChirL := by
  have hminus :
      (1 - Complex.I • chir) * (1 - Complex.I • chir) =
        (2 : ℂ) • (1 - Complex.I • chir) := by
    have hu := i_chir_sq_local
    simp only [sub_mul, mul_sub, one_mul, mul_one, hu, two_smul]
    abel
  let a : ℂ := (2 : ℂ)⁻¹
  let x : Matrix (Fin 4) (Fin 4) ℂ := 1 - Complex.I • chir
  have ha : a * a * (2 : ℂ) = a := by
    dsimp [a]
    norm_num
  have hx : x * x = (2 : ℂ) • x := by
    simpa [x] using hminus
  change (a • x) * (a • x) = a • x
  calc
    (a • x) * (a • x) = (a * a) • (x * x) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = (a * a) • ((2 : ℂ) • x) := by rw [hx]
    _ = (a * a * (2 : ℂ)) • x := by rw [smul_smul]
    _ = a • x := by rw [ha]

#print axioms solution
