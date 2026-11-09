-- Prove2me | solution 1 for BookProof.QuadraticRotation.quadOpMat_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:13:21.741423+00:00
-- url     : https://prove2.me/submissions/808ccff0-254f-433d-841c-4f198da6dac7

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.quadOpMat_not_bounded
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_exists_rotConj
import Theorems.Thm_BookProof_QuadraticRotation_quadOpMat_rotConj_not_bounded
open BookProof.QuadraticRotation




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (hA0 : A ≠ 0) :
    ¬ ∃ K : ℝ, ∀ f : polyGaussCore (d := d), ‖quadOpMat A f‖ ≤ K * ‖(f : L2d d)‖ := by

  obtain ⟨O, c, hO, hAeq⟩ := exists_rotConj hA
  have hc : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hA0 (by
      rw [hAeq]
      ext k l
      simp [rotConj, hcon])
  obtain ⟨i, hci⟩ := hc
  rw [hAeq]
  exact quadOpMat_rotConj_not_bounded hO c hci
