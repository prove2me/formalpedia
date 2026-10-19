-- Prove2me | solution 1 for BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic_pure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:16.184311+00:00
-- url     : https://prove2.me/submissions/724cc3ac-f931-4b0d-88fc-f428a4b2ef24

-- Generated from ChapterTimeTranslation.lean — solution of BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic_pure
import Mathlib
import Definitions.Def_ChapterTimeTranslation
import Theorems.Thm_BookProof_ChapterTimeTranslation_trace_diff
import Theorems.Thm_BookProof_ChapterReconstruct_offDiag_unit_iff
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterTimeTranslation



open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : Matrix (Fin n) (Fin n) ℂ) :
    (∀ (a : Fin n) (Ψ : Fin n → ℂ), (∑ k : Fin n, ‖Ψ k‖ ^ 2) = 1 →
        (diagPart (rho Ψ) * measOp U a).trace = (rho Ψ * measOp U a).trace)
      ↔ IsDeterministic U := by

  show (∀ (a : Fin n) (Ψ : Fin n → ℂ), (∑ k : Fin n, ‖Ψ k‖ ^ 2) = 1 →
        (diagPart (rho Ψ) * measOp U a).trace = (rho Ψ * measOp U a).trace)
      ↔ IsDeterministic (fun i j => U i j)
  rw [← offDiag_unit_iff]
  constructor
  · intro h a Ψ hΨ
    have hd := trace_diff U a Ψ
    rw [h a Ψ hΨ, sub_self] at hd
    exact hd.symm
  · intro h a Ψ hΨ
    have hd := trace_diff U a Ψ
    rw [h a Ψ hΨ, sub_eq_zero] at hd
    exact hd.symm
