-- Prove2me | solution 1 for BookProof.ChapterA3.differentiable_det
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:09:06.838746+00:00
-- url     : https://prove2.me/submissions/d3f3c9bc-a8f4-4d28-b5d3-284417e69711

-- Generated from ChapterA3f.lean — solution of BookProof.ChapterA3.differentiable_det
import Mathlib
import Definitions.Def_ChapterA3f
open BookProof.ChapterA3



open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution :
    Differentiable ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) := by

  have heq : (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
      = fun M => ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, M (σ i) i := by
    funext M; exact Matrix.det_apply M
  rw [heq]
  fun_prop
