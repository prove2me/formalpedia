-- Prove2me | solution 1 for BookProof.ChapterA3.hasDerivAt_det_line
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:09:18.733542+00:00
-- url     : https://prove2.me/submissions/84df134b-3169-4464-b45a-f8b6caa848e6

-- Generated from ChapterA3f.lean — solution of BookProof.ChapterA3.hasDerivAt_det_line
import Mathlib
import Definitions.Def_ChapterA3f
open BookProof.ChapterA3



open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := by

  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℝ, ∀ t : ℝ,
      (1 + t • A).det = 1 + A.trace * t + P.eval t * t ^ 2 := by
    exact ⟨ _, fun t => Matrix.det_one_add_smul t A ⟩;
  norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, Polynomial.differentiableAt, hP ];
  convert HasDerivAt.add ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id
      ( 0 : ℝ ) ) ( hasDerivAt_const _ _ ) ) ) ( HasDerivAt.mul ( hasDerivAt_id ( 0 : ℝ ) ) (
          HasDerivAt.mul ( hasDerivAt_id ( 0 : ℝ ) ) ( P.hasDerivAt 0 ) ) ) using 1 <;>
      (first | rfl | norm_num)
