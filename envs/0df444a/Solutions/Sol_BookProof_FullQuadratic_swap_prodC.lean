-- Prove2me | solution 1 for BookProof.FullQuadratic.swap_prodC
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T13:57:12.532212+00:00
-- url     : https://prove2.me/submissions/9bd63bdc-e5ff-4765-9c77-67794420af1f

-- Generated from ChapterFullQuadraticEsa.lean — solution of BookProof.FullQuadratic.swap_prodC
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Theorems.Thm_BookProof_FullQuadratic_swap_prod
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
theorem solution (a : Fin d →₀ ℕ) (i j : Fin d) :
    ((a j : ℂ)) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)
      = ((a i : ℂ)) * (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℂ) := by

  have h := swap_prod a i j
  exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) h
