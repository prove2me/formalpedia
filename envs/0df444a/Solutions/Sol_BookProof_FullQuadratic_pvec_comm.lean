-- Prove2me | solution 1 for BookProof.FullQuadratic.pvec_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T13:56:42.426998+00:00
-- url     : https://prove2.me/submissions/b24ef579-7e65-4571-be81-9884534091aa

-- Generated from ChapterFullQuadraticEsa.lean — solution of BookProof.FullQuadratic.pvec_comm
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

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (i j : Fin d) : pvec (d := d) i j = pvec j i := by
  rw [pvec, pvec, add_comm]
