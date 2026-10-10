-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq_of_unit_entries
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:11:35.381395+00:00
-- url     : https://prove2.me/submissions/7565eae9-9a15-4ae0-b988-b23c6e924b09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq_of_unit_entries
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
import Theorems.Thm_BookProof_ChapterScaledDotProduct_rademacherMean_dot_sq
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterScaledDotProduct



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {k : Fin d → ℝ} (hk : ∀ i, (k i) ^ 2 = 1) :
    rademacherMean (fun x => (dot (signVec x) k) ^ 2) = (d : ℝ) := by

  rw [rademacherMean_dot_sq, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hk i]
  simp
