-- Prove2me | solution 1 for BookProof.QuadraticRotation.quadOpMat_rotConj_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:04:45.747266+00:00
-- url     : https://prove2.me/submissions/0c8dba53-c7e5-43d7-a1de-08bea730e045

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Theorems.Thm_BookProof_QuadraticRotation_quadOpMat_essentiallySelfAdjoint
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
open BookProof.HermiteProductCore
open BookProof.QuadraticRotation
open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
noncomputable section
variable {d : ℕ}
theorem solution {O : Matrix (Fin d) (Fin d) ℝ}
    (hO : Oᵀ * O = 1) (c : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (quadOpMat (rotConj O c)) := by
  apply BookProof.QuadraticRotation.quadOpMat_essentiallySelfAdjoint
  ext k l
  simp only [conjTranspose_apply, star_trivial, rotConj]
  exact Finset.sum_congr rfl fun i _ => by ring
