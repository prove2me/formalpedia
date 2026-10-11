-- Prove2me | solution 1 for BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:14.385422+00:00
-- url     : https://prove2.me/submissions/6debf468-de7c-4992-bfc2-2d346f2b5999
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterTimeTranslation.lean — solution of BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic
import Mathlib
import Definitions.Def_ChapterTimeTranslation
import Theorems.Thm_BookProof_ChapterTimeTranslation_trace_diff
import Theorems.Thm_BookProof_ChapterReconstruct_offDiag_eq_zero_iff_isDeterministic
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterTimeTranslation



open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : Matrix (Fin n) (Fin n) ℂ) :
    (∀ (a : Fin n) (Ψ : Fin n → ℂ),
        (diagPart (rho Ψ) * measOp U a).trace = (rho Ψ * measOp U a).trace)
      ↔ IsDeterministic U := by

  show (∀ (a : Fin n) (Ψ : Fin n → ℂ),
        (diagPart (rho Ψ) * measOp U a).trace = (rho Ψ * measOp U a).trace)
      ↔ IsDeterministic (fun i j => U i j)
  rw [← offDiag_eq_zero_iff_isDeterministic]
  constructor
  · intro h a Ψ
    have hd := trace_diff U a Ψ
    rw [h a Ψ, sub_self] at hd
    exact hd.symm
  · intro h a Ψ
    have hd := trace_diff U a Ψ
    rw [h a Ψ, sub_eq_zero] at hd
    exact hd.symm
