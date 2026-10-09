-- Prove2me | solution 1 for BookProof.ChapterAttentionOVCircuit.mulVec_headOutput
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:29:29.480576+00:00
-- url     : https://prove2.me/submissions/270ce7ad-bb69-4a9d-a596-487f7bf15c6f

-- Generated from ChapterAttentionOVCircuit.lean — solution of BookProof.ChapterAttentionOVCircuit.mulVec_headOutput
import Mathlib
import Definitions.Def_ChapterAttentionOVCircuit
import Theorems.Thm_BookProof_ChapterAttentionOutput_headOutput_eq_sum
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionOutput
open BookProof.ChapterAttentionOVCircuit



open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n p m : ℕ}

variable {d n p m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (A : Matrix (Fin p) (Fin n) ℝ) (beta : ℝ) (s : Fin m → ℝ)
    (v : Fin m → (Fin n → ℝ)) :
    A *ᵥ headOutput beta s v = headOutput beta s (fun j => A *ᵥ v j) := by

  rw [headOutput_eq_sum, headOutput_eq_sum, Matrix.mulVec_sum]
  exact Finset.sum_congr rfl fun j _ => Matrix.mulVec_smul A (scoreSoftmax beta s j) (v j)
