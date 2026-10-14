-- Prove2me | solution 1 for BookProof.YangMillsAbelianEsa.coreRepPoly_equiv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:06:07.58999+00:00
-- url     : https://prove2.me/submissions/207a906e-278b-452f-bedd-bb4904be1b20

-- Generated from ChapterYangMillsAbelianEsa.lean — solution of BookProof.YangMillsAbelianEsa.coreRepPoly_equiv
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreEquiv_coe
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsAbelianEsa




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (p : MvPolynomial (Fin 99) ℂ) :
    (coreRepPoly 99).equiv p = coreEquiv p := by

  refine Subtype.ext ?_
  rw [(coreRepPoly 99).coe_equiv p, coreEquiv_coe p]
