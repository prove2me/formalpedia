-- Prove2me | solution 1 for BookProof.ChapterA3j.projChirR_idem
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T15:30:29.506038+00:00
-- url     : https://prove2.me/submissions/a17f12c7-bad2-4ab3-bd1c-cf9a06275a36

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

theorem solution : projChirR * projChirR = projChirR := by
  have hplus :
      (1 + Complex.I • chir) * (1 + Complex.I • chir) =
        (2 : ℂ) • (1 + Complex.I • chir) := by
    have hu := i_chir_sq_local
    simp only [add_mul, mul_add, one_mul, mul_one, hu, two_smul]
    abel
  let a : ℂ := (2 : ℂ)⁻¹
  let x : Matrix (Fin 4) (Fin 4) ℂ := 1 + Complex.I • chir
  have ha : a * a * (2 : ℂ) = a := by
    dsimp [a]
    norm_num
  have hx : x * x = (2 : ℂ) • x := by
    simpa [x] using hplus
  change (a • x) * (a • x) = a • x
  calc
    (a • x) * (a • x) = (a * a) • (x * x) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = (a * a) • ((2 : ℂ) • x) := by rw [hx]
    _ = (a * a * (2 : ℂ)) • x := by rw [smul_smul]
    _ = a • x := by rw [ha]

#print axioms solution
