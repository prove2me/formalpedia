-- Prove2me | solution 1 for BookProof.ChapterA3.upsilon_re
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:51:45.661713+00:00
-- url     : https://prove2.me/submissions/48e20977-e042-41ef-a81b-ed78a0e843ec

-- Generated from ChapterA4c.lean — solution of BookProof.ChapterA3.upsilon_re
import Mathlib
import Definitions.Def_ChapterA4c
import Theorems.Thm_BookProof_ChapterA3_upsilonC_real
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (μ ν : Fin 4) :
    ((Upsilon T μ ν : ℝ) : ℂ) = UpsilonC T μ ν := by

  unfold Upsilon
  simp only [Matrix.of_apply]
  exact (Complex.conj_eq_iff_re.mp (upsilonC_real T μ ν)) ▸ rfl
