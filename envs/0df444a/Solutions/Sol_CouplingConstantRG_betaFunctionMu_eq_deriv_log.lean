-- Prove2me | solution 1 for CouplingConstantRG.betaFunctionMu_eq_deriv_log
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:26:38.584633+00:00
-- url     : https://prove2.me/submissions/ac667161-8faf-4091-a1f9-4e28af52e419

import Mathlib
import Definitions.Def_CouplingConstantRGDefs

open CouplingConstantRG

theorem solution (g : ℝ → ℝ) (μ : ℝ) (hμ : 0 < μ) (hg : DifferentiableAt ℝ g μ) :
    betaFunctionMu g μ = deriv (fun t : ℝ => g (Real.exp t)) (Real.log μ) := by
  have hexp : Real.exp (Real.log μ) = μ := Real.exp_log hμ
  rw [betaFunctionMu]
  have hcomp :
      deriv (fun t : ℝ => g (Real.exp t)) (Real.log μ)
        = deriv g (Real.exp (Real.log μ)) * deriv Real.exp (Real.log μ) := by
    exact deriv_comp (Real.log μ) (by simpa [hexp] using hg) Real.differentiableAt_exp
  rw [hcomp, Real.deriv_exp, hexp]
  ring
