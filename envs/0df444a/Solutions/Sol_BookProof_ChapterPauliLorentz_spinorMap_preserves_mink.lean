-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.spinorMap_preserves_mink
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:31.915412+00:00
-- url     : https://prove2.me/submissions/eeb3e368-6a3a-4118-a006-5ec431e1963e

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.spinorMap_preserves_mink
import Mathlib
import Definitions.Def_ChapterPauliLorentz
import Theorems.Thm_BookProof_ChapterPauliLorentz_hermMat_isHermitian
import Theorems.Thm_BookProof_ChapterPauliLorentz_det_hermMat
import Theorems.Thm_BookProof_ChapterPauliLorentz_hermMat_vecOfMat
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1)
    (x : Fin 4 → ℝ) :
    mink (vecOfMat (Tᴴ * hermMat x * T)) = mink x := by

  set H := Tᴴ * hermMat x * T with hHdef
  have hHerm : Hᴴ = H := by
    rw [hHdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hermMat_isHermitian, Matrix.mul_assoc]
  -- the transformed matrix is again `hermMat` of its extracted 4-vector
  have hrecon : hermMat (vecOfMat H) = H := hermMat_vecOfMat hHerm
  -- determinants agree
  have hdet : (hermMat (vecOfMat H)).det = (hermMat x).det := by
    rw [hrecon, hHdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hT]
    simp
  rw [det_hermMat, det_hermMat] at hdet
  exact_mod_cast hdet
