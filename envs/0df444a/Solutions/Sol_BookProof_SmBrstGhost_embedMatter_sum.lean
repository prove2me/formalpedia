-- Prove2me | solution 1 for BookProof.SmBrstGhost.embedMatter_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:34:48.365806+00:00
-- url     : https://prove2.me/submissions/f6148165-5585-4cd7-bba8-8086aa05fa6f

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.embedMatter_sum
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
theorem solution {m : ℕ} {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin m) (Fin m) ℂ) :
    embedMatter m (∑ t ∈ s, M t) = ∑ t ∈ s, embedMatter m (M t) := by

  classical
  induction s using Finset.induction with
  | empty =>
      ext i j
      simp [embedMatter, Matrix.reindex_apply, Matrix.submatrix_apply]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      ext i j
      simp only [embedMatter, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]
      rcases finSumFinEquiv.symm i with u | u <;> rcases finSumFinEquiv.symm j with v | v <;> simp
