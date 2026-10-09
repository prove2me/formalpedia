-- Prove2me | solution 1 for BookProof.ChapterAttentionOVCircuit.ovOutput_eq_headOutput
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:30:03.071277+00:00
-- url     : https://prove2.me/submissions/aecde213-734b-4f88-a834-9af766bddbee

-- Generated from ChapterAttentionOVCircuit.lean — solution of BookProof.ChapterAttentionOVCircuit.ovOutput_eq_headOutput
import Mathlib
import Definitions.Def_ChapterAttentionOVCircuit
import Theorems.Thm_BookProof_ChapterAttentionOVCircuit_mulVec_headOutput
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionOutput
open BookProof.ChapterAttentionOVCircuit



open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n p m : ℕ}

variable {d n p m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (WO : Matrix (Fin n) (Fin d) ℝ)
    (WV : Matrix (Fin d) (Fin n) ℝ) (x : Fin m → (Fin n → ℝ)) :
    ovOutput beta s WO WV x = headOutput beta s (fun j => ovMatrix WO WV *ᵥ x j) := by

  rw [ovOutput, mulVec_headOutput]
  exact congrArg _ (funext fun j => by rw [ovMatrix, Matrix.mulVec_mulVec])
