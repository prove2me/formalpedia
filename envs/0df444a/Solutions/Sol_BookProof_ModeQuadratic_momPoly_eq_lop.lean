-- Prove2me | solution 1 for BookProof.ModeQuadratic.momPoly_eq_lop
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T16:12:55.70911+00:00
-- url     : https://prove2.me/submissions/1f47ba70-77ab-41d4-bbcd-bb9b30a48bee

-- Generated from ChapterModeQuadraticEsa.lean — solution of BookProof.ModeQuadratic.momPoly_eq_lop
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
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
open BookProof.HermiteProductBasis

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) :
    momPoly (d := d) i = (Complex.I / 2) • lop (-1) i := by

  refine LinearMap.ext fun p => ?_
  rw [momPoly_eq_cre_sub_ann]
  simp only [lop, LinearMap.smul_apply, LinearMap.add_apply, neg_smul, one_smul,
    LinearMap.neg_apply]
  rw [sub_eq_add_neg]
