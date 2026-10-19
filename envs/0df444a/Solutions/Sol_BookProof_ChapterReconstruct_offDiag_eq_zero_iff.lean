-- Prove2me | solution 1 for BookProof.ChapterReconstruct.offDiag_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:51:39.474958+00:00
-- url     : https://prove2.me/submissions/61c5ce15-6f36-4d6b-95c7-4a011a70de22

-- Generated from ChapterReconstruct.lean — solution of BookProof.ChapterReconstruct.offDiag_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterReconstruct
import Theorems.Thm_BookProof_ChapterReconstruct_offDiag_of_isDeterministicCol
import Theorems.Thm_BookProof_ChapterReconstruct_isDeterministicCol_of_offDiag
open BookProof.ChapterReconstruct



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : Fin n → Fin n → ℂ) (a : Fin n) :
    (∀ Ψ : Fin n → ℂ, offDiag U a Ψ = 0) ↔ IsDeterministicCol U a := ⟨isDeterministicCol_of_offDiag U a, offDiag_of_isDeterministicCol U a⟩
