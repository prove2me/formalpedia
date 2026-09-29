-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.backward_error_weyl_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:28:13.128129+00:00
-- url     : https://prove2.me/submissions/a3c5fd64-b8d8-460d-89fb-04787d415ed6

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.backward_error_weyl_symm
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
import Theorems.Thm_BookProof_SirkFinitePrecision_backward_error_weyl
open BookProof.SirkFinitePrecision







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T S : E →ₗ[ℂ] E} (hS : S.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {ε : ℝ} (hε : ∀ x : E, ‖T x - S x‖ ≤ ε * ‖x‖)
    {lam : ℝ} (hlam : HasRealEigenvalue T lam) :
    ∃ mu : ℝ, HasRealEigenvalue S mu ∧ |mu - lam| ≤ ε := by

  refine backward_error_weyl hS hn (S := T) (fun x => ?_) hlam
  rw [← norm_neg]
  simpa using hε x
