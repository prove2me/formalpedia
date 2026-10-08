-- Prove2me | solution 1 for BookProof.OperatorSeries.commForm_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:56:10.232986+00:00
-- url     : https://prove2.me/submissions/21ec730d-4268-4201-81c3-72b9d9b64b4b

-- Generated from ChapterOperatorSeriesEsa.lean — solution of BookProof.OperatorSeries.commForm_add
import Mathlib
import Definitions.Def_ChapterOperatorSeriesEsa
import Theorems.Thm_BookProof_OperatorSeries_commForm_eq_neg_two_im
open BookProof.OperatorSeries




open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (H₁ H₂ N : D →ₗ[ℂ] F) (x : D) :
    commForm (H₁ + H₂) N x = commForm H₁ N x + commForm H₂ N x := by

  rw [commForm_eq_neg_two_im, commForm_eq_neg_two_im, commForm_eq_neg_two_im]
  have : (H₁ + H₂) x = H₁ x + H₂ x := rfl
  rw [this, inner_add_left]
  simp [Complex.add_im]
  ring
