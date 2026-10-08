-- Prove2me | solution 1 for BookProof.OperatorSeries.commForm_eq_neg_two_im
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:55:43.880285+00:00
-- url     : https://prove2.me/submissions/883fa7a0-c997-4d51-b7f0-df369ba5f125

-- Generated from ChapterOperatorSeriesEsa.lean — solution of BookProof.OperatorSeries.commForm_eq_neg_two_im
import Mathlib
import Definitions.Def_ChapterOperatorSeriesEsa
open BookProof.OperatorSeries




open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (H N : D →ₗ[ℂ] F) (x : D) :
    commForm H N x = -2 * (inner ℂ (H x) (N x) : ℂ).im := by

  have hconj : (inner ℂ (N x) (H x) : ℂ) = (starRingEnd ℂ) (inner ℂ (H x) (N x) : ℂ) :=
    (inner_conj_symm (𝕜 := ℂ) _ _).symm
  rw [commForm, hconj]
  set z : ℂ := (inner ℂ (H x) (N x) : ℂ) with hz
  have : Complex.I * (z - (starRingEnd ℂ) z) = -2 * (z.im : ℂ) := by
    rw [Complex.sub_conj]
    push_cast
    rw [mul_comm]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [this]
  simp
