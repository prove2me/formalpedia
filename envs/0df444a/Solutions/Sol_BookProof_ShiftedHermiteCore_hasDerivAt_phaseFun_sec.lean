-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.hasDerivAt_phaseFun_sec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:27.413817+00:00
-- url     : https://prove2.me/submissions/23df62bc-2b86-4467-af21-8a475f2f3757

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.hasDerivAt_phaseFun_sec
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Theorems.Thm_BookProof_ShiftedHermiteCore_phaseFun_sec
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
theorem solution (k x : Vd d) (i : Fin d) :
    HasDerivAt (fun t : ℝ => phaseFun k (sec i x t))
      (phaseFun k x * (Complex.I * ((k i : ℝ) : ℂ))) (x i) := by

  have hlin : HasDerivAt
      (fun z : ℂ => Complex.I * (((k i : ℝ) : ℂ) * (z - ((x i : ℝ) : ℂ))))
      (Complex.I * ((k i : ℝ) : ℂ)) (((x i : ℝ)) : ℂ) := by
    simpa using
      ((((hasDerivAt_id (((x i : ℝ)) : ℂ)).sub_const (((x i : ℝ)) : ℂ)).const_mul
        (((k i : ℝ) : ℂ))).const_mul Complex.I)
  have hE : HasDerivAt
      (fun z : ℂ => Complex.exp (Complex.I * (((k i : ℝ) : ℂ) * (z - ((x i : ℝ) : ℂ)))))
      (Complex.I * ((k i : ℝ) : ℂ)) (((x i : ℝ)) : ℂ) := by
    simpa using hlin.cexp
  have hR := hE.comp_ofReal (z := x i)
  have hfun : (fun t : ℝ =>
        Complex.exp (Complex.I * (((k i : ℝ) : ℂ) * (((t : ℝ) : ℂ) - ((x i : ℝ) : ℂ)))))
      = fun t : ℝ => Complex.exp (Complex.I * (((k i * (t - x i) : ℝ)) : ℂ)) := by
    funext t
    congr 2
    push_cast
    ring
  rw [hfun] at hR
  have hmul := hR.const_mul (phaseFun k x)
  have hfun2 : (fun t : ℝ =>
        phaseFun k x * Complex.exp (Complex.I * (((k i * (t - x i) : ℝ)) : ℂ)))
      = fun t : ℝ => phaseFun k (sec i x t) := by
    funext t
    rw [phaseFun_sec]
  rwa [hfun2] at hmul
