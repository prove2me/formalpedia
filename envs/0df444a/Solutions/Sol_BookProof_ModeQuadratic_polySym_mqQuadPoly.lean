-- Prove2me | solution 1 for BookProof.ModeQuadratic.polySym_mqQuadPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T16:10:30.394358+00:00
-- url     : https://prove2.me/submissions/c2d02b0b-1779-41a8-9bd6-44f1f1ff108c

-- Generated from ChapterModeQuadraticEsa.lean — solution of BookProof.ModeQuadratic.polySym_mqQuadPoly
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Theorems.Thm_BookProof_HermiteRelative_polySym_sum
import Theorems.Thm_BookProof_HermiteRelative_polySym_momPoly
import Theorems.Thm_BookProof_HermiteRelative_polySym_mulXPoly
import Theorems.Thm_BookProof_YangMillsHermite_PolySym_add
import Theorems.Thm_BookProof_YangMillsHermite_PolySym_real_smul
import Theorems.Thm_BookProof_YangMillsHermite_weylProd_polySym
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterYangMillsHermite
open BookProof.ModeQuadratic




open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.YangMillsHermite

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (p q s : Fin d → ℝ) :
    BookProof.YangMillsHermite.PolySym (mqQuadPoly p q s) := by
  refine polySym_sum _ _ fun i _ => ?_
  refine ((BookProof.YangMillsHermite.weylProd_polySym (BookProof.HermiteRelative.polySym_momPoly i)
      (BookProof.HermiteRelative.polySym_momPoly i)).real_smul.add
    (BookProof.YangMillsHermite.weylProd_polySym (BookProof.HermiteRelative.polySym_mulXPoly i)
      (BookProof.HermiteRelative.polySym_mulXPoly i)).real_smul).add ?_
  exact (BookProof.YangMillsHermite.weylProd_polySym (BookProof.HermiteRelative.polySym_mulXPoly i)
    (BookProof.HermiteRelative.polySym_momPoly i)).real_smul
