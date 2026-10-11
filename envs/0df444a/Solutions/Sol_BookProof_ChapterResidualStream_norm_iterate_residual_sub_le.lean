-- Prove2me | solution 1 for BookProof.ChapterResidualStream.norm_iterate_residual_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:52:12.283103+00:00
-- url     : https://prove2.me/submissions/320a4f02-0191-48c7-a111-117d10133b68

-- Generated from ChapterResidualStream.lean — solution of BookProof.ChapterResidualStream.norm_iterate_residual_sub_le
import Mathlib
import Definitions.Def_ChapterResidualStream
import Theorems.Thm_BookProof_ChapterResidualStream_norm_residual_sub_self
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterResidualStream



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]

set_option maxHeartbeats 1000000 in
theorem solution {f : E → E} {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) (n : ℕ)
    (x : E) :
    ‖(residual f)^[n] x - x‖ ≤ n * C := by

  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (residual f)^[n + 1] x = residual f ((residual f)^[n] x) := by
        rw [Function.iterate_succ_apply']
      have hsplit : (residual f)^[n + 1] x - x
          = (residual f ((residual f)^[n] x) - (residual f)^[n] x)
            + ((residual f)^[n] x - x) := by
        rw [hstep]
        abel
      have h1 : ‖residual f ((residual f)^[n] x) - (residual f)^[n] x‖ ≤ C := by
        rw [norm_residual_sub_self]
        exact hf _
      calc ‖(residual f)^[n + 1] x - x‖
          ≤ ‖residual f ((residual f)^[n] x) - (residual f)^[n] x‖
            + ‖(residual f)^[n] x - x‖ := by
            rw [hsplit]
            exact norm_add_le _ _
        _ ≤ C + n * C := add_le_add h1 ih
        _ = (n + 1 : ℕ) * C := by push_cast; ring
