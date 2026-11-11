-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger58_factorised_second_order_ode_weighted_first_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:13:34.354452+00:00
-- url     : https://prove2.me/submissions/b912145f-c480-4b6e-97eb-b9848e62aab0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gsource15_exponential_derivative_comparison
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set
noncomputable section

/-- A factorised second-order differential inequality makes its first-order
    exponential integrating factor antitone. -/
theorem solution
    (r l u : ℝ) (w : ℝ → ℝ)
    (hw : ∀ y : ℝ, u ≤ y → HasDerivAt w (deriv w y) y)
    (hw2 : ∀ y : ℝ, u ≤ y →
      HasDerivAt (deriv w) (iteratedDeriv 2 w y) y)
    (hode : ∀ y : ℝ, u ≤ y →
      iteratedDeriv 2 w y - (r + l) * deriv w y +
        r * l * w y ≤ 0) :
    ∀ y : ℝ, u ≤ y →
      Real.exp (-(r * y)) * (deriv w y - l * w y) ≤
        Real.exp (-(r * u)) * (deriv w u - l * w u) := by
  let F : ℝ → ℝ := fun t => deriv w t - l * w t
  have hFder (t : ℝ) (ht : u ≤ t) :
      HasDerivAt F (iteratedDeriv 2 w t - l * deriv w t) t := by
    exact (hw2 t ht).sub ((hw t ht).const_mul l)
  have hFineq (t : ℝ) (ht : u ≤ t) : deriv F t ≤ r * F t := by
    rw [(hFder t ht).deriv]
    dsimp [F]
    nlinarith [hode t ht]
  intro y hy
  have hcomp : F y ≤ Real.exp (r * (y - u)) * F u :=
    avram_gsource15_exponential_derivative_comparison F u y r hy
      (by intro t ht; rw [(hFder t ht.1).deriv]; exact hFder t ht.1)
      (by intro t ht; exact hFineq t ht.1)
  have h := mul_le_mul_of_nonneg_left hcomp (Real.exp_pos (-(r * y))).le
  change Real.exp (-(r * y)) * F y ≤ Real.exp (-(r * u)) * F u
  calc
    Real.exp (-(r * y)) * F y ≤
        Real.exp (-(r * y)) * (Real.exp (r * (y - u)) * F u) := h
    _ = Real.exp (-(r * u)) * F u := by
      rw [← mul_assoc, ← Real.exp_add]
      have hid : -(r * y) + r * (y - u) = -(r * u) := by ring
      rw [hid]
