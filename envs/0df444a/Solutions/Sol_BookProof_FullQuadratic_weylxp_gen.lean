-- Prove2me | solution 1 for BookProof.FullQuadratic.weylxp_gen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T13:57:43.197124+00:00
-- url     : https://prove2.me/submissions/64e0a206-1472-467a-87d5-f0e088b193c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFullQuadraticEsa.lean — solution of BookProof.FullQuadratic.weylxp_gen
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Theorems.Thm_BookProof_FullQuadratic_weylProd_smul_apply
import Theorems.Thm_BookProof_ModeQuadratic_momPoly_eq_lop
import Theorems.Thm_BookProof_ModeQuadratic_mulXPoly_eq_lop
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
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
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
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin d) (a : Fin d →₀ ℕ) :
    BookProof.YangMillsHermite.weylProd (mulXPoly i) (momPoly j) (hermiteMv a)
      = (Complex.I / 2) •
          BookProof.YangMillsHermite.weylProd (lop 1 i) (lop (-1) j) (hermiteMv a) := by

  rw [mulXPoly_eq_lop, momPoly_eq_lop]
  have h := weylProd_smul_apply (d := d) 1 (Complex.I / 2) (lop 1 i) (lop (-1) j) (hermiteMv a)
  rw [one_smul] at h
  rw [h, one_mul]
