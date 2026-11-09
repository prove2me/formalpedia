-- Prove2me | solution 1 for BookProof.FullQuadratic.polySym_fqQuadPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T16:09:38.523327+00:00
-- url     : https://prove2.me/submissions/f2418667-d016-40fd-a9a6-9dd6bc1f0932

-- Generated from ChapterFullQuadraticEsa.lean — solution of BookProof.FullQuadratic.polySym_fqQuadPoly
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
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
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterYangMillsHermite
open BookProof.FullQuadratic




open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.CarlemanSimplex
open BookProof.ModeQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.YangMillsHermite

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (P Q S : Fin d → Fin d → ℝ) :
    BookProof.YangMillsHermite.PolySym (fqQuadPoly P Q S) := by
  refine polySym_sum _ _ fun i _ => ?_
  refine polySym_sum _ _ fun j _ => ?_
  refine ((BookProof.YangMillsHermite.weylProd_polySym (BookProof.HermiteRelative.polySym_momPoly i)
      (BookProof.HermiteRelative.polySym_momPoly j)).real_smul.add
    (BookProof.YangMillsHermite.weylProd_polySym (BookProof.HermiteRelative.polySym_mulXPoly i)
      (BookProof.HermiteRelative.polySym_mulXPoly j)).real_smul).add ?_
  exact (BookProof.YangMillsHermite.weylProd_polySym (BookProof.HermiteRelative.polySym_mulXPoly i)
    (BookProof.HermiteRelative.polySym_momPoly j)).real_smul
