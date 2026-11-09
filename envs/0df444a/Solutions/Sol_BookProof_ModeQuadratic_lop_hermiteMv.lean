-- Prove2me | solution 1 for BookProof.ModeQuadratic.lop_hermiteMv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T14:00:43.239487+00:00
-- url     : https://prove2.me/submissions/bccd7310-6341-455f-ab18-3d2c52adc14f

-- Generated from ChapterModeQuadraticEsa.lean — solution of BookProof.ModeQuadratic.lop_hermiteMv
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Theorems.Thm_BookProof_HermiteProductBasis_crePoly_hermiteMv
import Theorems.Thm_BookProof_HermiteProductBasis_pderiv_hermiteMv
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
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
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (t : ℂ) (i : Fin d) (b : Fin d →₀ ℕ) :
    lop t i (hermiteMv b)
      = hermiteMv (b + Finsupp.single i 1) + (t * (b i : ℂ)) • hermiteMv (b - Finsupp.single i 1)
      := by
  simp only [lop, LinearMap.add_apply, LinearMap.smul_apply, annPoly_apply]
  rw [crePoly_hermiteMv, pderiv_hermiteMv, smul_smul]
