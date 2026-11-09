-- Prove2me | solution 1 for BookProof.FullQuadratic.hermiteMvNorm_add_pvec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T13:57:53.963777+00:00
-- url     : https://prove2.me/submissions/ccee510f-fe42-4cfc-8220-fcedaeb6e117

-- Generated from ChapterFullQuadraticEsa.lean — solution of BookProof.FullQuadratic.hermiteMvNorm_add_pvec
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Theorems.Thm_BookProof_FullQuadratic_add_pvec_eq
import Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvNorm_add_single
import Definitions.Def_ChapterHermiteProductCore
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
import Definitions.Def_ChapterHermiteProductBasis
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
open BookProof.HermiteProductBasis

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin d) (a : Fin d →₀ ℕ) :
    hermiteMvNorm (a + pvec i j) = hermiteMvNorm a * rcp a i j := by

  rw [← add_pvec_eq, hermiteMvNorm_add_single i (a + Finsupp.single j 1),
    hermiteMvNorm_add_single j a, rcp]
  ring
