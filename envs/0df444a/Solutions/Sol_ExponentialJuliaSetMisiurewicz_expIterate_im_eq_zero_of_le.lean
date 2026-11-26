-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.expIterate_im_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:41.434176+00:00
-- url     : https://prove2.me/submissions/fc195a16-ab84-4e32-922e-a593bce4bbd4

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
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
theorem _root_.solution {z : ℂ} {n : ℕ} (h : (expIterate n z).im = 0) :
    ∀ m, n ≤ m → (expIterate m z).im = 0 := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => simpa using h
  | succ d ih =>
      have hidx : n + (d + 1) = (n + d) + 1 := by omega
      rw [hidx, expIterate_succ, Complex.exp_im, ih (by omega), Real.sin_zero, mul_zero]
end ExponentialJuliaSetMisiurewicz
