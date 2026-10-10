-- Prove2me | solution 1 for BookProof.QuadraticRotation.rotConj_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:43:33.528537+00:00
-- url     : https://prove2.me/submissions/17de63e2-829d-4660-b8f0-c5e6be3bab8a

import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
open BookProof.QuadraticRotation
open MeasureTheory MvPolynomial Matrix

noncomputable section

theorem solution {d : ℕ} (O : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) :
    rotConj O c = O * Matrix.diagonal c * Oᵀ := by
  ext k l
  simp only [rotConj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_ite]
