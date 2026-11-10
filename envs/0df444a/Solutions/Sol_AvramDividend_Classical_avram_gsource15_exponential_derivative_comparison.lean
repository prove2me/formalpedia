-- Prove2me | solution 1 for AvramDividend.Classical.avram_gsource15_exponential_derivative_comparison
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:17:57.35219+00:00
-- url     : https://prove2.me/submissions/cd18c639-27b9-442e-9b90-85ec13cac771

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

theorem solution
    (S : ℝ → ℝ) (a b K : ℝ) (hab : a ≤ b)
    (hDer : ∀ y ∈ Set.Icc a b, HasDerivAt S (deriv S y) y)
    (hIneq : ∀ y ∈ Set.Icc a b, deriv S y ≤ K * S y) :
    S b ≤ Real.exp (K * (b - a)) * S a := by
  let F : ℝ → ℝ := fun t => Real.exp (-K * t) * S t
  have hFder (x : ℝ) (hx : x ∈ Set.Icc a b) :
      HasDerivAt F (Real.exp (-K * x) * (deriv S x - K * S x)) x := by
    have hlin : HasDerivAt (fun t : ℝ => -K * t) (-K) x := by
      convert (hasDerivAt_id x).const_mul (-K) using 1 <;> first | rfl | ring | simp
    have he : HasDerivAt (fun t : ℝ => Real.exp (-K * t))
        (Real.exp (-K * x) * (-K)) x := by
      convert (Real.hasDerivAt_exp (-K * x)).comp x hlin using 1 <;> first | rfl | ring | simp
    convert he.mul (hDer x hx) using 1 <;> first | rfl | ring | simp
  have hFcont : ContinuousOn F (Set.Icc a b) := by
    intro x hx
    exact (hFder x hx).continuousAt.continuousWithinAt
  have hFdiff : DifferentiableOn ℝ F (interior (Set.Icc a b)) := by
    intro x hx
    exact (hFder x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hFsign : ∀ x ∈ interior (Set.Icc a b), deriv F x ≤ 0 := by
    intro x hx
    have hxi : x ∈ Set.Icc a b := interior_subset hx
    rw [(hFder x hxi).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos _)) (sub_nonpos.mpr (hIneq x hxi))
  have hAnti : AntitoneOn F (Set.Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b) hFcont hFdiff hFsign
  have hFa : a ∈ Set.Icc a b := ⟨le_refl _, hab⟩
  have hFb : b ∈ Set.Icc a b := ⟨hab, le_refl _⟩
  have hBound : F b ≤ F a := hAnti hFa hFb hab
  change Real.exp (-K * b) * S b ≤ Real.exp (-K * a) * S a at hBound
  have hc : Real.exp (K * b) * Real.exp (-K * b) = 1 := by
    rw [← Real.exp_add]
    have he : K * b + -K * b = 0 := by ring
    rw [he, Real.exp_zero]
  have hs : Real.exp (K * b) * Real.exp (-K * a) =
      Real.exp (K * (b - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    S b = (Real.exp (K * b) * Real.exp (-K * b)) * S b := by
      rw [hc]
      ring
    _ = Real.exp (K * b) * (Real.exp (-K * b) * S b) := by ring
    _ ≤ Real.exp (K * b) * (Real.exp (-K * a) * S a) :=
      mul_le_mul_of_nonneg_left hBound (le_of_lt (Real.exp_pos _))
    _ = (Real.exp (K * b) * Real.exp (-K * a)) * S a := by ring
    _ = Real.exp (K * (b - a)) * S a := by rw [hs]
