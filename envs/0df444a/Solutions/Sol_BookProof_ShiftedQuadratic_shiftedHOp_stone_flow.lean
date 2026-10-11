-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.shiftedHOp_stone_flow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:16.836127+00:00
-- url     : https://prove2.me/submissions/4c913afe-ca33-4b7d-ad99-b61d0e4caa3d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.shiftedHOp_stone_flow
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_symmetric
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_essentiallySelfAdjoint
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedCore_dense
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
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
theorem solution (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (shiftedHOp (shiftVec c b) (boostVec c b') c b b') T.op ∧
        IsStoneFlow T U :=
  exists_stone_flow_of_esa _ (shiftedCore_dense c b b') (shiftedHOp_symmetric c b b' hc)
      (shiftedHOp_essentiallySelfAdjoint c b b' hc)
