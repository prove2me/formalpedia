-- Prove2me | solution 1 for BirkhoffGlobalSection.jacobi_partial_momentum_two
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:17:44.055706+00:00
-- url     : https://prove2.me/submissions/68a6e329-d2bd-4803-8ddc-019dd727ea3a

import Theorems.Thm_BirkhoffGlobalSection_jacobi_momentum_two_line_derivative
import Theorems.Thm_BirkhoffGlobalSection_partial_derivative_eq_update_deriv

open BirkhoffGlobalSection

theorem solution (μ : ℝ) (s : Phase)
    (hdiff : DifferentiableAt ℝ (jacobiHamiltonian μ) s) :
    partialDerivative (jacobiHamiltonian μ) s 3 = s 3 + s 0 := by
  rw [partial_derivative_eq_update_deriv (jacobiHamiltonian μ) s 3 hdiff]
  exact (jacobi_momentum_two_line_derivative μ s).deriv
