-- Prove2me | solution 1 for BookProof.ModeQuadratic.add_single_one_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T14:00:06.886062+00:00
-- url     : https://prove2.me/submissions/dbea8411-289e-4d02-8978-96b8139c8f06

-- Generated from ChapterModeQuadraticEsa.lean — solution of BookProof.ModeQuadratic.add_single_one_one
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
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

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (i : Fin d) (a : Fin d →₀ ℕ) :
    a + Finsupp.single i 1 + Finsupp.single i 1 = a + Finsupp.single i 2 := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]
