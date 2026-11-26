-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.conj_image_up_of_down
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:13.537199+00:00
-- url     : https://prove2.me/submissions/3ebfbdc3-55bd-4863-ad75-212a8e0aa8d0

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
theorem _root_.solution {V : Set ℂ} {n : ℕ}
    (h : ∀ z ∈ V, (expIterate n z).im < 0) :
    ∀ z ∈ (starRingEnd ℂ) '' V, 0 < (expIterate n z).im := by
  rintro z ⟨y, hy, rfl⟩
  rw [expIterate_conj]
  simp only [Complex.conj_im, Left.neg_pos_iff]
  exact h y hy
end ExponentialJuliaSetMisiurewicz
