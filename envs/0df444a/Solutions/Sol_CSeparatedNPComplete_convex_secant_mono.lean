-- Prove2me | solution 1 for CSeparatedNPComplete.convex_secant_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:46:09.05488+00:00
-- url     : https://prove2.me/submissions/bd166728-78c6-4621-adb9-558b6e407b8a

module
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Order.Monotone.Extension
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Definitions.Def_CSeparatedNPComplete_ConvexSlopes
section
@[expose] public section
namespace CSeparatedNPComplete
private theorem secant_symm (f : ℝ → ℝ) (x y : ℝ) :
    (f y - f x) / (y - x) = (f x - f y) / (x - y) := by
  rw [← neg_div_neg_eq]
  simp
end CSeparatedNPComplete
end
end

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    {x₁ x₂ y₁ y₂ : ℝ} (hx₁ : x₁ ∈ s) (hx₂ : x₂ ∈ s)
    (hy₁ : y₁ ∈ s) (hy₂ : y₂ ∈ s)
    (h₁ : x₁ ≠ y₁) (h₂ : x₂ ≠ y₂) (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    (f y₁ - f x₁) / (y₁ - x₁) ≤ (f y₂ - f x₂) / (y₂ - x₂) := by
  by_cases h : x₁ = y₂
  · subst y₂
    rw [secant_symm f x₂ x₁]
    exact hf.secant_mono hx₁ hy₁ hx₂ h₁.symm h₂ (hy.trans hx)
  · calc
      (f y₁ - f x₁) / (y₁ - x₁) ≤ (f y₂ - f x₁) / (y₂ - x₁) :=
        hf.secant_mono hx₁ hy₁ hy₂ h₁.symm (Ne.symm h) hy
      _ = (f x₁ - f y₂) / (x₁ - y₂) := secant_symm f x₁ y₂
      _ ≤ (f x₂ - f y₂) / (x₂ - y₂) :=
        hf.secant_mono hy₂ hx₁ hx₂ h h₂ hx
      _ = (f y₂ - f x₂) / (y₂ - x₂) := secant_symm f y₂ x₂
end CSeparatedNPComplete
