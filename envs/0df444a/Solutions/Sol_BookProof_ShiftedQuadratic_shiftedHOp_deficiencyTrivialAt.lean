-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.shiftedHOp_deficiencyTrivialAt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:13.879063+00:00
-- url     : https://prove2.me/submissions/1cc00f92-33ad-4007-bf42-c9416ac13be6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.shiftedHOp_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_hermiteTLp
import Theorems.Thm_BookProof_HyperbolicQuadratic_deficiencyTrivialAt_of_diagonal
import Theorems.Thm_BookProof_ShiftedHermiteCore_hermiteTLp_mem_coreT
import Theorems.Thm_BookProof_ShiftedHermiteCore_hermiteTLp_total
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
theorem solution (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) {z : ℂ}
    (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCoreT (shiftVec c b) (boostVec c b'))
      (shiftedHOp (shiftVec c b) (boostVec c b') c b b') z :=
  deficiencyTrivialAt_of_diagonal (hermiteTLp (shiftVec c b) (boostVec c b'))
      (fun α => quadSymbol c α + shiftConst c b b') (hermiteTLp_total _ _) _
      (hermiteTLp_mem_coreT _ _) (fun α h => shiftedHOp_hermiteTLp c b b' hc α h) hz
