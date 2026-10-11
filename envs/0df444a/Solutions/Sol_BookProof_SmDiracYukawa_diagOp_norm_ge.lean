-- Prove2me | solution 1 for BookProof.SmDiracYukawa.diagOp_norm_ge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:06:50.555078+00:00
-- url     : https://prove2.me/submissions/0adee12a-7d3a-4847-bcad-cff69bf5e2ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.diagOp_norm_ge
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
theorem solution {d : Finset (Fin n) → ℝ} (hd : ∀ S, 1 ≤ d S) (ψ : FermiFock n) :
    ‖ψ‖ ≤ ‖diagOp d ψ‖ := by

  have hsq : ‖ψ‖ ^ 2 ≤ ‖diagOp d ψ‖ ^ 2 := by
    rw [diagOp_normSq, normSq_eq_sum]
    refine Finset.sum_le_sum fun S _ => ?_
    have h1 : (1:ℝ) ≤ (d S) ^ 2 := by nlinarith [hd S]
    nlinarith [norm_nonneg (ψ S), sq_nonneg (‖ψ S‖)]
  nlinarith [norm_nonneg ψ, norm_nonneg (diagOp d ψ)]
