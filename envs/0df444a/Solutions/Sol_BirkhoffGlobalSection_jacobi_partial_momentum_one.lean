-- Prove2me | solution 1 for BirkhoffGlobalSection.jacobi_partial_momentum_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:34:10.591991+00:00
-- url     : https://prove2.me/submissions/9720b6fd-d5c1-45ff-9b10-0952462e2b84

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Theorems.Thm_BirkhoffGlobalSection_partial_derivative_eq_update_deriv

open BirkhoffGlobalSection

theorem solution (μ : ℝ) (s : Phase)
    (hdiff : DifferentiableAt ℝ (jacobiHamiltonian μ) s) :
    partialDerivative (jacobiHamiltonian μ) s 2 = s 2 - s 1 := by
  rw [partial_derivative_eq_update_deriv (jacobiHamiltonian μ) s 2 hdiff]
  let C : ℝ := (s 3) ^ 2 / 2 + (s 0) * (s 3) -
      (1 - μ) / Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2) -
      μ / Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)
  have hfun : (fun t : ℝ => jacobiHamiltonian μ (Function.update s (2 : Fin 4) t)) =
      (fun t : ℝ => t ^ 2 / 2 + (-(s 1)) * t + C) := by
    funext t
    simp [C, jacobiHamiltonian, Function.update_apply]
    ring
  rw [hfun]
  have hquad := (((hasDerivAt_pow 2 (s 2)).div_const 2).add
      ((hasDerivAt_id (x := s 2)).const_mul (-(s 1)))).add_const C
  have hline : HasDerivAt (fun t : ℝ => t ^ 2 / 2 + (-(s 1)) * t + C)
      (s 2 - s 1) (s 2) := by
    convert hquad using 1 <;> first | rfl | (funext t; ring) | ring
  exact hline.deriv
