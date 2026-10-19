-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.wave_indefiniteQuadratic_linear_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:42:46.507674+00:00
-- url     : https://prove2.me/submissions/4841a375-a8f1-49c9-81e2-dd48d0e8aa40

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.wave_indefiniteQuadratic_linear_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_essentiallySelfAdjoint
import Theorems.Thm_BookProof_ShiftedQuadratic_minkowskiCoeff_ne_zero
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
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
theorem solution (n : ℕ)
    (b b' : Fin (1 + n) → ℝ) :
    EssentiallySelfAdjointOn
      (polyGaussCoreT (shiftVec (minkowskiCoeff n) b) (boostVec (minkowskiCoeff n) b'))
      (shiftedHOp (shiftVec (minkowskiCoeff n) b) (boostVec (minkowskiCoeff n) b')
        (minkowskiCoeff n) b b') := shiftedHOp_essentiallySelfAdjoint _ b b' (minkowskiCoeff_ne_zero n)
