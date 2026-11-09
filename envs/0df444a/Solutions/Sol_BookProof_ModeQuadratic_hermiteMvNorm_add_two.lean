-- Prove2me | solution 1 for BookProof.ModeQuadratic.hermiteMvNorm_add_two
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T14:02:13.524285+00:00
-- url     : https://prove2.me/submissions/b02104e9-87b0-4c32-91db-a21442e296c7

-- Generated from ChapterModeQuadraticEsa.lean — solution of BookProof.ModeQuadratic.hermiteMvNorm_add_two
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Theorems.Thm_BookProof_ModeQuadratic_add_single_one_one
import Theorems.Thm_BookProof_ModeQuadratic_add_single_apply_self
import Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvNorm_add_single
import Definitions.Def_ChapterHermiteProductCore
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
theorem solution (i : Fin d) (a : Fin d →₀ ℕ) :
    hermiteMvNorm (a + Finsupp.single i 2)
      = hermiteMvNorm a * Real.sqrt ((a i : ℝ) + 1) * Real.sqrt ((a i : ℝ) + 2) := by

  rw [← add_single_one_one i a, hermiteMvNorm_add_single i (a + Finsupp.single i 1),
    hermiteMvNorm_add_single i a, add_single_apply_self]
  push_cast
  ring_nf
