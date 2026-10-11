-- Prove2me | solution 1 for BookProof.SmBrstGhost.embedMatter_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:34:47.114506+00:00
-- url     : https://prove2.me/submissions/f2ca03f1-b1bc-4af1-9552-ec32ecb668a9

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.embedMatter_smul
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
theorem solution (m : ℕ) (c : ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    embedMatter m (c • M) = c • embedMatter m M := by

  ext i j
  simp only [embedMatter, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
    smul_eq_mul]
  rcases finSumFinEquiv.symm i with u | u <;> rcases finSumFinEquiv.symm j with v | v <;> simp
