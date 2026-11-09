-- Prove2me | solution 1 for BookProof.FullQuadratic.weylProd_smul_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T13:57:23.972708+00:00
-- url     : https://prove2.me/submissions/d914139a-6115-4724-9b39-1381a6f02537

-- Generated from ChapterFullQuadraticEsa.lean — solution of BookProof.FullQuadratic.weylProd_smul_apply
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
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
open BookProof.YangMillsHermite

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (c c' : ℂ) (A B : Module.End ℂ (MvPolynomial (Fin d) ℂ))
    (p : MvPolynomial (Fin d) ℂ) :
    BookProof.YangMillsHermite.weylProd (c • A) (c' • B) p
      = (c * c') • BookProof.YangMillsHermite.weylProd A B p := by
  simp only [BookProof.YangMillsHermite.weylProd, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.comp_apply, map_smul, smul_smul]
  rw [mul_comm c' c]
  module
