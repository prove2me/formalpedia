-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.rotConj_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:53:51.413172+00:00
-- url     : https://prove2.me/submissions/f7d5ada9-687b-4973-9b26-2ff8a116cfe4

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.rotConj_isHermitian
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ShiftedQuadraticMatrix




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (O : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) :
    (rotConj O c).IsHermitian := by

  change (rotConj O c)ᴴ = rotConj O c
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, rotConj]
  exact Finset.sum_congr rfl fun l _ => by ring
