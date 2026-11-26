-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.noreal_conj_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:11.846634+00:00
-- url     : https://prove2.me/submissions/962063b3-76e2-4e15-a536-ba166c9fce67

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_conj
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {V : Set ℂ}
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0) :
    ∀ (n : ℕ), ∀ z ∈ (starRingEnd ℂ) '' V, (expIterate n z).im ≠ 0 := by
  rintro n z ⟨y, hy, rfl⟩ hval
  rw [expIterate_conj] at hval
  simp only [Complex.conj_im, neg_eq_zero] at hval
  exact hnoreal n y hy hval
end ExponentialJuliaSetMisiurewicz
