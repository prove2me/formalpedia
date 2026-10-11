-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.shiftedCore_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:15.797711+00:00
-- url     : https://prove2.me/submissions/c7507457-a9d0-4a10-9a9d-191d35313033

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.shiftedCore_dense
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedHermiteCore_polyGaussCoreT_dense
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadratic




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c b b' : Fin d → ℝ) :
    Dense ((polyGaussCoreT (shiftVec c b) (boostVec c b')
      : Submodule ℂ (L2d d)) : Set (L2d d)) := polyGaussCoreT_dense _ _
