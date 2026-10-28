-- Prove2me | solution 1 for AvramDividend.Classical.exponential_tilt_preserves_cross_derivative_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:40:07.04423+00:00
-- url     : https://prove2.me/submissions/d79033ac-09c6-44f1-ba7f-908a44a917b0

import Theorems.Thm_AvramDividend_Classical_esscher_exponential_derivative
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- A positive exponential Esscher tilt preserves the local cross-slope order. -/
theorem solution
    (f : ℝ → ℝ) (φ x y : ℝ)
    (hcross : deriv f y * f x ≤ deriv f x * f y)
    (hdx : DifferentiableAt ℝ f x)
    (hdy : DifferentiableAt ℝ f y) :
    deriv (fun z : ℝ => Real.exp (-φ * z) * f z) y *
        (Real.exp (-φ * x) * f x) ≤
      deriv (fun z : ℝ => Real.exp (-φ * z) * f z) x *
        (Real.exp (-φ * y) * f y) := by
  let E : ℝ → ℝ := fun z => Real.exp (-φ * z)
  let g : ℝ → ℝ := fun z => E z * f z
  have hdg (z : ℝ) (hdz : DifferentiableAt ℝ f z) :
      deriv g z = E z * (deriv f z - φ * f z) := by
    have hE : DifferentiableAt ℝ E z := by
      dsimp [E]
      fun_prop
    have hproduct : deriv g z =
        deriv E z * f z + E z * deriv f z := by
      have hgf : g = E * f := by
        funext t
        rfl
      rw [hgf]
      exact deriv_mul hE hdz
    have hEd : deriv E z = E z * (-φ) := by
      simpa [E] using (esscher_exponential_derivative φ z)
    rw [hproduct, hEd]
    ring
  have hEpos (z : ℝ) : 0 < E z := Real.exp_pos _
  have hweight : 0 ≤ E y * E x :=
    le_of_lt (mul_pos (hEpos y) (hEpos x))
  have hcompare :
      deriv f y * f x - φ * f y * f x ≤
        deriv f x * f y - φ * f x * f y := by
    nlinarith [hcross]
  change deriv g y * g x ≤ deriv g x * g y
  calc
    deriv g y * g x =
        (E y * E x) * (deriv f y * f x - φ * f y * f x) := by
          rw [hdg y hdy]
          dsimp [g]
          ring
    _ ≤ (E y * E x) *
        (deriv f x * f y - φ * f x * f y) :=
          mul_le_mul_of_nonneg_left hcompare hweight
    _ = deriv g x * g y := by
      rw [hdg x hdx]
      dsimp [g]
      ring
