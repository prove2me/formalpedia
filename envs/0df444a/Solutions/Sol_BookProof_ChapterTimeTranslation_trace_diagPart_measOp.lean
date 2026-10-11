-- Prove2me | solution 1 for BookProof.ChapterTimeTranslation.trace_diagPart_measOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:02.563771+00:00
-- url     : https://prove2.me/submissions/1887069d-f106-47d8-b4cf-9707f7d76f82

-- Generated from ChapterTimeTranslation.lean — solution of BookProof.ChapterTimeTranslation.trace_diagPart_measOp
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
    (diagPart (rho Ψ) * measOp U a).trace =
      ∑ k : Fin n,
        (starRingEnd ℂ) (U k a) * Ψ k * (starRingEnd ℂ) (Ψ k) * U k a := by

  unfold diagPart; simp only [trace, rho, of_apply, diag_apply, mul_apply, measOp_apply, ite_mul,
      zero_mul, sum_ite_eq, mem_univ, ↓reduceIte] ;
  exact Finset.sum_congr rfl fun _ _ => by ring;
