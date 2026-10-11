-- Prove2me | solution 1 for BookProof.ChapterTimeTranslation.trace_diff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:13.407934+00:00
-- url     : https://prove2.me/submissions/a56028e7-2b22-441b-8e19-7ec9918a5d4c

-- Generated from ChapterTimeTranslation.lean — solution of BookProof.ChapterTimeTranslation.trace_diff
import Mathlib
import Definitions.Def_ChapterTimeTranslation
import Theorems.Thm_BookProof_ChapterTimeTranslation_trace_rho_measOp
import Theorems.Thm_BookProof_ChapterTimeTranslation_trace_diagPart_measOp
import Theorems.Thm_BookProof_ChapterReconstruct_offDiag_eq
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterTimeTranslation



open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (Ψ : Fin n → ℂ) :
    (rho Ψ * measOp U a).trace - (diagPart (rho Ψ) * measOp U a).trace
      = offDiag U a Ψ := by

  rw [trace_rho_measOp, trace_diagPart_measOp, offDiag_eq (U := fun i j => U i j)]
