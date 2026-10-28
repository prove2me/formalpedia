-- Prove2me | solution 1 for FinancialDerivatives.FD06.log_spot_derivative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:11:09.048163+00:00
-- url     : https://prove2.me/submissions/ca1fd095-e5d7-43f0-87aa-886d10ab0787

import Mathlib


theorem solution (f : ℝ → ℝ) (S : ℝ) (hS : 0 < S) (hf : DifferentiableAt ℝ f (Real.log S)) : deriv (fun x => f (Real.log x)) S = deriv f (Real.log S) / S := by
  have := (hf.hasDerivAt.comp S (Real.hasDerivAt_log hS.ne'))
  rw [show (fun x => f (Real.log x)) = f ∘ Real.log from rfl, this.deriv]; field_simp
