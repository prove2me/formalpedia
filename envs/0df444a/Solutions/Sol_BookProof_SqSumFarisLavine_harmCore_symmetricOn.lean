-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.harmCore_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-02T17:42:26.629985+00:00
-- url     : https://prove2.me/submissions/f6fe0be0-e536-4396-99c7-ed13a7822091

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.harmCore_symmetricOn
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteQuadraticEsa
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.SqSumFarisLavine




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.HermiteQuadraticEsa
open BookProof.QgOuterFock
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution : SymmetricOn (polyGaussCore (d := D)) (harmCore (d := D)) := hamCore_symmetricOn _ _ _
