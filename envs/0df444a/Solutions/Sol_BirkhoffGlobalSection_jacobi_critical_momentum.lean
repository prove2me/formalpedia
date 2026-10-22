-- Prove2me | solution 1 for BirkhoffGlobalSection.jacobi_critical_momentum
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T19:10:08.919867+00:00
-- url     : https://prove2.me/submissions/f0aa567a-2cb0-4372-b952-058c24005930

import Mathlib.Tactic.Linarith
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_momentum_one
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_momentum_two

open BirkhoffGlobalSection

theorem solution (μ : ℝ) (s : Phase)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s) :
    s 2 = s 1 ∧ s 3 = -s 0 := by
  have hz₂ : partialDerivative (jacobiHamiltonian μ) s 2 = 0 := by
    simp [partialDerivative, hcrit.2]
  have hz₃ : partialDerivative (jacobiHamiltonian μ) s 3 = 0 := by
    simp [partialDerivative, hcrit.2]
  have h₂ := jacobi_partial_momentum_one μ s hcrit.1
  have h₃ := jacobi_partial_momentum_two μ s hcrit.1
  constructor <;> linarith
