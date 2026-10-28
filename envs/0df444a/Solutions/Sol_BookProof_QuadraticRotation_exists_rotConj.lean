-- Prove2me | solution 1 for BookProof.QuadraticRotation.exists_rotConj
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:39:54.577235+00:00
-- url     : https://prove2.me/submissions/ae4e08cb-54ee-47a5-9e1f-b9054ea75d32

import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.exists_rotConj
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}
theorem solution {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    ∃ (O : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ), Oᵀ * O = 1 ∧ A = rotConj O c := by
  set U : Matrix (Fin d) (Fin d) ℝ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  refine ⟨U, hA.eigenvalues, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using hU
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    conv_lhs => rw [h]
    ext k l
    simp [rotConj, Matrix.mul_apply, Matrix.diagonal, U, Matrix.star_apply]
