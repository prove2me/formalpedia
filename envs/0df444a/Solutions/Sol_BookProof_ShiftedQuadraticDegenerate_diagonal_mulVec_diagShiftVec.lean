-- Prove2me | solution 1 for BookProof.ShiftedQuadraticDegenerate.diagonal_mulVec_diagShiftVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:33:54.880982+00:00
-- url     : https://prove2.me/submissions/2533b2b6-0ef0-4f74-928d-88ad69ae129a

-- Generated from ChapterShiftedQuadraticDegenerate.lean — solution of BookProof.ShiftedQuadraticDegenerate.diagonal_mulVec_diagShiftVec
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
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

theorem solution {c w : Fin d → ℝ} (hcw : ∀ i, c i = 0 → w i = 0)
    (i : Fin d) : ∑ j, (Matrix.diagonal c) i j * (diagShiftVec c w) j = w i := by
  classical
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj])
    (by simp)]
  by_cases h : c i = 0
  · simp [Matrix.diagonal_apply_eq, diagShiftVec, h, hcw i h]
  · simp only [Matrix.diagonal_apply_eq, diagShiftVec, WithLp.ofLp_toLp, h, if_false]
    field_simp
