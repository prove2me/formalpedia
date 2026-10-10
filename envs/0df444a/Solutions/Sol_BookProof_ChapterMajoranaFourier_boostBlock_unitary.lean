-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.boostBlock_unitary
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:28:33.168376+00:00
-- url     : https://prove2.me/submissions/faaaff1f-9ed4-4021-9e15-11eccbc8c713

import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterMajoranaFourier
open Matrix

theorem solution {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : Aᴴ = A) (hA2 : A * A = 1)
    {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    (boostBlock c s A)ᴴ * boostBlock c s A = 1 := by
  simp only [boostBlock, fromBlocks_conjTranspose, fromBlocks_multiply]
  simp only [hA, conjTranspose_smul, conjTranspose_one, star_neg, Complex.star_def,
    Complex.conj_ofReal, smul_mul_smul_comm, hA2, mul_one, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fromBlocks, Matrix.one_apply, Matrix.smul_apply, add_smul, mul_comm,
      ← Complex.ofReal_mul, ← Complex.ofReal_add] <;>
    (first | exact hcs | (convert hcs using 1; ring))
