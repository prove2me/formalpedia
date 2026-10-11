-- Prove2me | solution 1 for BookProof.SmBrstGhost.embedMatter_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:34:45.95414+00:00
-- url     : https://prove2.me/submissions/8537f465-1d0b-43a9-be01-15c3c03b78c9

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.embedMatter_sub
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
    embedMatter m (M - P) = embedMatter m M - embedMatter m P := by

  ext i j
  simp only [embedMatter, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]
  rcases finSumFinEquiv.symm i with u | u <;> rcases finSumFinEquiv.symm j with v | v <;> simp
