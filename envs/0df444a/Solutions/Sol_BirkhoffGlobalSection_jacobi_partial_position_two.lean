-- Prove2me | solution 1 for BirkhoffGlobalSection.jacobi_partial_position_two
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:51:52.316757+00:00
-- url     : https://prove2.me/submissions/837f7348-deed-4b9f-8287-d344e990c0b6

import Theorems.Thm_BirkhoffGlobalSection_partial_derivative_eq_update_deriv
import Theorems.Thm_BirkhoffGlobalSection_jacobi_collisionFree_differentiableAt
import Theorems.Thm_BirkhoffGlobalSection_jacobi_position_two_line_derivative

open BirkhoffGlobalSection

theorem solution (μ : ℝ) (s : Phase)
    (hfree : collisionFree μ s) :
    partialDerivative (jacobiHamiltonian μ) s 1 =
      -s 2 + (1 - μ) * (s 1) /
        (Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 +
      μ * (s 1) /
        (Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 := by
  rw [partial_derivative_eq_update_deriv (jacobiHamiltonian μ) s 1
    (jacobi_collisionFree_differentiableAt μ s hfree)]
  exact (jacobi_position_two_line_derivative μ s hfree).deriv
