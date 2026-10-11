-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.shiftedHPoly_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:07.983841+00:00
-- url     : https://prove2.me/submissions/300d5c21-9edd-4a4b-9439-0dc8194f0d08

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.shiftedHPoly_apply
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadratic




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a k : Vd d) (c b b' : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) :
    shiftedHPoly a k c b b' p
      = ∑ i, (((c i : ℝ) : ℂ) • oscTPoly a k i p + ((b i : ℝ) : ℂ) • mulXTPoly a i p
          + ((b' i : ℝ) : ℂ) • momTPoly k i p) := by

  simp [shiftedHPoly, LinearMap.sum_apply]
