-- Prove2me | solution 1 for BookProof.ShiftedQuadraticDegenerate.diagonal_degenerate_essentiallySelfAdjoint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:34:09.911498+00:00
-- url     : https://prove2.me/submissions/1d0b0b18-a5f3-408f-b571-1df5099b936c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — solution of BookProof.ShiftedQuadraticDegenerate.diagonal_degenerate_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_shiftedHMatOp_essentiallySelfAdjoint_of_equilibrium
import Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_diagonal_mulVec_diagShiftVec
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadraticDegenerate




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.ShiftedQuadraticMatrix
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.StoneEigenflow

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c b b' : Fin d → ℝ)
    (hb : ∀ i, c i = 0 → b i = 0) (hb' : ∀ i, c i = 0 → b' i = 0) :
    EssentiallySelfAdjointOn
      (polyGaussCoreT (diagShiftVec c fun i => -2 * b i)
        (diagShiftVec c fun i => -(b' i) / 2))
      (shiftedHMatOp (diagShiftVec c fun i => -2 * b i)
        (diagShiftVec c fun i => -(b' i) / 2) (Matrix.diagonal c) b b') :=
  shiftedHMatOp_essentiallySelfAdjoint_of_equilibrium (Matrix.isHermitian_diagonal_iff.mpr
        (fun i => IsSelfAdjoint.all (c i))) b b' _ _
      (diagonal_mulVec_diagShiftVec fun i hi => by rw [hb i hi]; ring)
      (diagonal_mulVec_diagShiftVec fun i hi => by rw [hb' i hi]; norm_num)
