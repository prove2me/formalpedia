-- Prove2me | solution 1 for BookProof.ChapterTimeTranslation.trace_rho_measOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:01.006214+00:00
-- url     : https://prove2.me/submissions/cc8b4588-5acb-41bf-8e20-9e15c4d07cec

-- Generated from ChapterTimeTranslation.lean — solution of BookProof.ChapterTimeTranslation.trace_rho_measOp
import Mathlib
import Definitions.Def_ChapterTimeTranslation
import Theorems.Thm_BookProof_ChapterTimeTranslation_measOp_apply
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterTimeTranslation



open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (Ψ : Fin n → ℂ) :
    (rho Ψ * measOp U a).trace =
      (∑ k : Fin n, (starRingEnd ℂ) (U k a) * Ψ k) *
        (∑ b : Fin n, (starRingEnd ℂ) (Ψ b) * U b a) := by

  -- Expand the trace of the product.
  simp [Matrix.trace, Matrix.mul_apply, rho, measOp_apply];
  simp only [mul_comm, mul_left_comm, Finset.mul_sum _ _ _]
