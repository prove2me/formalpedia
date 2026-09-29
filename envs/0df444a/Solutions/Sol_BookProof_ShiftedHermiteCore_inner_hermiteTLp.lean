-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.inner_hermiteTLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T01:22:32.220602+00:00
-- url     : https://prove2.me/submissions/1ce0e0a2-3228-4147-9ad7-c455fe624cab

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.inner_hermiteTLp
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.ShiftedHermiteCore











open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a k : Vd d) (α β : Fin d →₀ ℕ) :
    (inner ℂ (hermiteTLp a k α) (hermiteTLp a k β) : ℂ)
      = (inner ℂ (hermiteMvLp (d := d) α) (hermiteMvLp (d := d) β) : ℂ) := by

  rw [hermiteTLp, hermiteTLp, hermiteMvLp, hermiteMvLp, inner_smul_left, inner_smul_right,
    inner_smul_left, inner_smul_right, inner_pgLpT]
