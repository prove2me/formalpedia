-- Prove2me | solution 2 for Complex.negative_imaginary_exponential_eq_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:25:56.688181+00:00
-- url     : https://prove2.me/submissions/531adfaa-0044-4543-a383-fe4004e805df

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
noncomputable section
open scoped BigOperators FourierTransform


omit [Fact (0 < d)]
theorem solution (x m : EuclideanSpace ℝ (Fin d)) :
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ))) =
    (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  have h2c : (starRingEnd ℂ) 2 = 2 := by apply Complex.ext <;> simp
  simp [Complex.conj_ofReal, h2c]

