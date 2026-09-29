-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.gaussInt_re
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T13:22:17.82285+00:00
-- url     : https://prove2.me/submissions/16f89736-db2c-4404-9ff4-dcb17486c0e3

-- Generated from ChapterGaussCoreQuadBounds.lean — solution of BookProof.GaussCoreQuadBounds.gaussInt_re
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds









open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (r : MvPolynomial (Fin D) ℂ) :
    (gaussInt r).re
      = ∫ x : Vd D, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r).re * gaussWD x := by

  rw [gaussInt, ← Complex.reCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_gwFun r)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.mul_re]
