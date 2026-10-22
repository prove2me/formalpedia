-- Prove2me | solution 1 for BirkhoffGlobalSection.jacobi_partial_position_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:05:02.219994+00:00
-- url     : https://prove2.me/submissions/285fe589-5633-4d1c-8d51-46b2221ac453

import Theorems.Thm_BirkhoffGlobalSection_partial_derivative_eq_update_deriv
import Theorems.Thm_BirkhoffGlobalSection_jacobi_collisionFree_differentiableAt
import Theorems.Thm_BirkhoffGlobalSection_jacobi_position_one_line_derivative

open BirkhoffGlobalSection

theorem solution (μ : ℝ) (s : Phase)
    (hfree : collisionFree μ s) :
    partialDerivative (jacobiHamiltonian μ) s 0 =
      s 3 + (1 - μ) * (s 0 + μ) /
        (Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 +
      μ * (s 0 - 1 + μ) /
        (Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 := by
  rw [partial_derivative_eq_update_deriv (jacobiHamiltonian μ) s 0
    (jacobi_collisionFree_differentiableAt μ s hfree)]
  exact (jacobi_position_one_line_derivative μ s hfree).deriv
