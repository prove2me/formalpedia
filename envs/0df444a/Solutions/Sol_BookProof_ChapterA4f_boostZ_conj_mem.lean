-- Prove2me | solution 1 for BookProof.ChapterA4f.boostZ_conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:08:13.544151+00:00
-- url     : https://prove2.me/submissions/1c614f60-8bf8-420c-ab34-f83a43c07c25

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.boostZ_conj_mem
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4f
import Definitions.Def_ChapterA4d
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem solution {l : ℂ} (hl : l ≠ 0) {T : Matrix (Fin 2) (Fin 2) ℂ}
    (hT : T ∈ SEtwo) : boostZ l * T * boostZ l⁻¹ ∈ SEtwo := by
  rcases hT with ⟨hd, hz, hn⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, hd]
    simp [boostZ, Matrix.det_fin_two, hl]
  · simp [boostZ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hz]
  · convert hn using 1
    congr 1
    simp [boostZ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    field_simp

#print axioms solution
