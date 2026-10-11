-- Prove2me | solution 1 for BookProof.ChapterReconstruct.offDiag_eq_zero_iff_isDeterministic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:51:53.573995+00:00
-- url     : https://prove2.me/submissions/7031a179-e457-4643-9c30-5668c130a3bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterReconstruct.lean — solution of BookProof.ChapterReconstruct.offDiag_eq_zero_iff_isDeterministic
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
theorem solution (U : Fin n → Fin n → ℂ) :
    (∀ (a : Fin n) (Ψ : Fin n → ℂ), offDiag U a Ψ = 0) ↔ IsDeterministic U := by

  constructor
  · intro h a
    exact isDeterministicCol_of_offDiag U a (h a)
  · intro h a Ψ
    exact offDiag_of_isDeterministicCol U a (h a) Ψ
