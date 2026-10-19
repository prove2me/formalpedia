-- Prove2me | solution 1 for BookProof.SmDiracYukawa.diagOp_quadForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:06:49.523714+00:00
-- url     : https://prove2.me/submissions/20840531-2509-4722-a71d-02b2676102a9

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.diagOp_quadForm_eq
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_diagOp_inner
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
theorem solution (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) :
    (inner ℂ ψ (diagOp d ψ) : ℂ).re = ∑ S : Finset (Fin n), d S * ‖ψ S‖ ^ 2 := by

  rw [diagOp_inner, Complex.re_sum]
  exact Finset.sum_congr rfl fun S _ => Complex.ofReal_re _
