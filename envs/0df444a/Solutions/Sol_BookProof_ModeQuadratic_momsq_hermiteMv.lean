-- Prove2me | solution 1 for BookProof.ModeQuadratic.momsq_hermiteMv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T14:01:17.76606+00:00
-- url     : https://prove2.me/submissions/b8262588-5950-46e5-8061-972e986fafd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterModeQuadraticEsa.lean — solution of BookProof.ModeQuadratic.momsq_hermiteMv
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Theorems.Thm_BookProof_ModeQuadratic_momPoly_eq_lop
import Theorems.Thm_BookProof_ModeQuadratic_lop_lop_hermiteMv
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
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
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (a : Fin d →₀ ℕ) :
    BookProof.YangMillsHermite.weylProd (momPoly i) (momPoly i) (hermiteMv a)
      = (-(1 / 4 : ℂ)) • hermiteMv (a + Finsupp.single i 2)
        + ((2 * (a i : ℂ) + 1) / 4) • hermiteMv a
        + (-(1 / 4 : ℂ) * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ)))
            • hermiteMv (a - Finsupp.single i 2) := by

  have hI : (Complex.I / 2) * (Complex.I / 2) = -(1 / 4 : ℂ) := by
    rw [div_mul_div_comm, Complex.I_mul_I]
    norm_num
  rw [momPoly_eq_lop, BookProof.YangMillsHermite.weylProd]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, map_smul,
    smul_smul, hI]
  rw [lop_lop_hermiteMv (-1) (-1) i a]
  push_cast
  module
