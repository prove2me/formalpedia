-- Prove2me | solution 1 for BookProof.SmDiracYukawa.diagOp_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:06:51.521436+00:00
-- url     : https://prove2.me/submissions/c2594bf0-e7ea-4851-9834-5b5c9af7488d

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.diagOp_norm_le
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_diagOp_normSq
import Theorems.Thm_BookProof_SmCar_normSq_eq_sum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {d : Finset (Fin n) → ℝ} {Om : ℝ} (hOm : 0 ≤ Om)
    (hd : ∀ S, |d S| ≤ Om) (ψ : FermiFock n) : ‖diagOp d ψ‖ ≤ Om * ‖ψ‖ := by

  have hsq : ‖diagOp d ψ‖ ^ 2 ≤ (Om * ‖ψ‖) ^ 2 := by
    rw [diagOp_normSq, mul_pow, normSq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun S _ => ?_
    have h1 : (d S) ^ 2 ≤ Om ^ 2 := by
      have := hd S
      nlinarith [abs_nonneg (d S), sq_abs (d S)]
    nlinarith [sq_nonneg ‖ψ S‖, norm_nonneg (ψ S)]
  nlinarith [norm_nonneg (diagOp d ψ), mul_nonneg hOm (norm_nonneg ψ)]
