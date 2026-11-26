-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.expIterate_real_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:06.029454+00:00
-- url     : https://prove2.me/submissions/3e393392-f310-467b-a369-f2cdab06d8cc

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
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
theorem _root_.solution {p : ℂ} (hp : p.im = 0) (m : ℕ) :
    (expIterate m p).im = 0 ∧ p.re + m ≤ (expIterate m p).re := by
  induction m with
  | zero => simpa [expIterate] using hp
  | succ m ih =>
      obtain ⟨him, hre⟩ := ih
      constructor
      · rw [expIterate_succ, Complex.exp_im, him, Real.sin_zero, mul_zero]
      · rw [expIterate_succ, Complex.exp_re, him, Real.cos_zero, mul_one]
        have hexp := Real.add_one_le_exp (expIterate m p).re
        push_cast
        linarith
end ExponentialJuliaSetMisiurewicz
