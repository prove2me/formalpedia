-- Prove2me | solution 1 for BirkhoffGlobalSection.noncollinear_critical_vertical_balance
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:43:55.775026+00:00
-- url     : https://prove2.me/submissions/856352f1-203a-4087-a70f-6a3daeab4ad7

import Mathlib.Tactic.Ring
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_position_two
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum

open BirkhoffGlobalSection

theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (hoffaxis : s 1 ≠ 0) :
    (1 - μ) / (Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 +
      μ / (Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 = 1 := by
  let r₁ : ℝ := Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2)
  let r₂ : ℝ := Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)
  have hp : s 2 = s 1 := (jacobi_critical_momentum μ s hcrit).1
  have hz : partialDerivative (jacobiHamiltonian μ) s 1 = 0 := by
    simp [partialDerivative, hcrit.2]
  have hforce : 0 = -(s 1) + (1 - μ) * (s 1) / r₁ ^ 3 +
      μ * (s 1) / r₂ ^ 3 := by
    simpa only [hz, hp] using jacobi_partial_position_two μ s hfree
  have hfactor : (s 1) * (((1 - μ) / r₁ ^ 3 + μ / r₂ ^ 3) - 1) = 0 := by
    calc
      _ = -(s 1) + (1 - μ) * (s 1) / r₁ ^ 3 + μ * (s 1) / r₂ ^ 3 := by ring
      _ = 0 := hforce.symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hoffaxis)
