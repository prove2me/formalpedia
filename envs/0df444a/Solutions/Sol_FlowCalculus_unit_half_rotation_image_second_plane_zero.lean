-- Prove2me | solution 1 for FlowCalculus.unit_half_rotation_image_second_plane_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T10:15:24.090887+00:00
-- url     : https://prove2.me/submissions/3cb6cedf-bab6-42c3-ba14-51b5552641a0

import Definitions.Def_GrayStability_HopfFamily
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open GrayStability
open scoped ContDiff

theorem solution (f : E 4 → E 4) (hf : ContDiff ℝ ∞ f)
    (hR : ∀ y ∈ levelSet unitSphereEquation,
      fderiv ℝ f y ![-y 1, y 0, -y 3, y 2] =
        ![-(f y) 1, (f y) 0, -(f y) 3 / 2, (f y) 2 / 2]) :
    ∀ y ∈ levelSet unitSphereEquation, (f y) 2 = 0 ∧ (f y) 3 = 0 := by
  intro y hy
  let γ : ℝ → E 4 := fun s =>
    ![Real.cos s * y 0 - Real.sin s * y 1,
      Real.sin s * y 0 + Real.cos s * y 1,
      Real.cos s * y 2 - Real.sin s * y 3,
      Real.sin s * y 2 + Real.cos s * y 3]
  have hγmem (s : ℝ) : γ s ∈ levelSet unitSphereEquation := by
    have hys : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 = 1 := by
      have h := congrFun hy 0
      simp [unitSphereEquation, Fin.sum_univ_succ] at h
      linarith
    change unitSphereEquation (γ s) = 0
    ext i
    simp [unitSphereEquation, γ, Fin.sum_univ_succ]
    nlinarith [Real.sin_sq_add_cos_sq s,
      sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2), sq_nonneg (y 3)]
  have hγder (s : ℝ) : HasDerivAt γ ![-(γ s) 1, (γ s) 0, -(γ s) 3, (γ s) 2] s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [γ]
    · convert ((Real.hasDerivAt_cos s).mul_const (y 0)).sub
        ((Real.hasDerivAt_sin s).mul_const (y 1)) using 1 <;> (try (apply funext; intro r)) <;> (try dsimp) <;> first | rfl | ring
    · convert ((Real.hasDerivAt_sin s).mul_const (y 0)).add
        ((Real.hasDerivAt_cos s).mul_const (y 1)) using 1 <;> (try (apply funext; intro r)) <;> (try dsimp) <;> first | rfl | ring
    · convert ((Real.hasDerivAt_cos s).mul_const (y 2)).sub
        ((Real.hasDerivAt_sin s).mul_const (y 3)) using 1 <;> (try (apply funext; intro r)) <;> (try dsimp) <;> first | rfl | ring
    · convert ((Real.hasDerivAt_sin s).mul_const (y 2)).add
        ((Real.hasDerivAt_cos s).mul_const (y 3)) using 1 <;> (try (apply funext; intro r)) <;> (try dsimp) <;> first | rfl | ring
  have hcomp (s : ℝ) : HasDerivAt (fun r => f (γ r))
      ![-(f (γ s)) 1, (f (γ s)) 0, -(f (γ s)) 3 / 2, (f (γ s)) 2 / 2] s := by
    rw [← hR (γ s) (hγmem s)]
    exact (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt s (hγder s)
  let a : ℝ → ℝ := fun s => f (γ s) 2
  let b : ℝ → ℝ := fun s => f (γ s) 3
  have ha (s : ℝ) : HasDerivAt a (-b s / 2) s := by
    simpa [a, b] using (hasDerivAt_pi.mp (hcomp s) 2)
  have hb (s : ℝ) : HasDerivAt b (a s / 2) s := by
    simpa [a, b] using (hasDerivAt_pi.mp (hcomp s) 3)
  have hc (s : ℝ) : HasDerivAt (fun r : ℝ => Real.cos (r / 2))
      (-Real.sin (s / 2) / 2) s := by
    convert (Real.hasDerivAt_cos (s / 2)).comp s ((hasDerivAt_id s).div_const 2) using 1 <;> (try (apply funext; intro r)) <;> (try dsimp) <;> first | rfl | ring
  have hs (s : ℝ) : HasDerivAt (fun r : ℝ => Real.sin (r / 2))
      (Real.cos (s / 2) / 2) s := by
    convert (Real.hasDerivAt_sin (s / 2)).comp s ((hasDerivAt_id s).div_const 2) using 1 <;> (try (apply funext; intro r)) <;> (try dsimp) <;> first | rfl | ring
  have hu (s : ℝ) : HasDerivAt
      (fun r => Real.cos (r / 2) * a r + Real.sin (r / 2) * b r) 0 s := by
    convert ((hc s).mul (ha s)).add ((hs s).mul (hb s)) using 1 <;> (try (apply funext; intro r)) <;> (try dsimp) <;> first | rfl | ring
  have hv (s : ℝ) : HasDerivAt
      (fun r => -Real.sin (r / 2) * a r + Real.cos (r / 2) * b r) 0 s := by
    convert (((hs s).neg).mul (ha s)).add ((hc s).mul (hb s)) using 1 <;> (try (apply funext; intro r)) <;> (try dsimp) <;> first | rfl | ring
  have huconst := is_const_of_deriv_eq_zero (fun s => (hu s).differentiableAt)
    (fun s => (hu s).deriv) (2 * Real.pi) 0
  have hvconst := is_const_of_deriv_eq_zero (fun s => (hv s).differentiableAt)
    (fun s => (hv s).deriv) (2 * Real.pi) 0
  have hγ0 : γ 0 = y := by ext i; fin_cases i <;> simp [γ]
  have hγP : γ (2 * Real.pi) = y := by
    ext i; fin_cases i <;> simp [γ, Real.cos_two_pi, Real.sin_two_pi]
  have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
  simp only [hhalf, Real.cos_pi, Real.sin_pi, zero_div, Real.cos_zero,
    Real.sin_zero, a, b, hγ0, hγP] at huconst hvconst
  constructor <;> linarith
