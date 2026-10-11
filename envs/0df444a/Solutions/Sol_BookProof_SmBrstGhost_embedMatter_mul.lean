-- Prove2me | solution 1 for BookProof.SmBrstGhost.embedMatter_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:34:44.744753+00:00
-- url     : https://prove2.me/submissions/cd645723-e513-4eda-8d88-7988f26432d1

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.embedMatter_mul
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (m : ℕ) (M P : Matrix (Fin m) (Fin m) ℂ) :
    embedMatter m M * embedMatter m P = embedMatter m (M * P) := by

  simp only [embedMatter, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv (Matrix.fromBlocks M 0 0 0) (Matrix.fromBlocks P 0 0 0)
    finSumFinEquiv.symm finSumFinEquiv.symm finSumFinEquiv.symm]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp
