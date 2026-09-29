-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.phaseFun_sec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:20.408635+00:00
-- url     : https://prove2.me/submissions/c3ce2f29-d86a-497d-a2a4-e93a9fe08da9

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.phaseFun_sec
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Theorems.Thm_BookProof_ShiftedHermiteCore_phaseArg_sec
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
theorem solution (k x : Vd d) (i : Fin d) (t : ℝ) :
    phaseFun k (sec i x t)
      = phaseFun k x * Complex.exp (Complex.I * (((k i * (t - x i) : ℝ)) : ℂ)) := by

  rw [phaseFun, phaseFun, phaseArg_sec, ← Complex.exp_add]
  congr 1
  push_cast
  ring
