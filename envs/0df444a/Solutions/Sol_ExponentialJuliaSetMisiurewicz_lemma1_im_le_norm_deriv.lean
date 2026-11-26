-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma1_im_le_norm_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:10.242584+00:00
-- url     : https://prove2.me/submissions/1b1d7ff7-c0ed-4302-b36a-eb1dfe2746c3

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_deriv_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_abs_im_exp_le
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
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    |(expIterate n z).im| ≤ ‖deriv (expIterate n) z‖ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero =>
      rw [deriv_expIterate_succ]
      simp [expIterate]
      exact Complex.abs_im_le_norm (Complex.exp z)
  | succ m ih =>
      have hindex : 1 + (m + 1) = (1 + m) + 1 := by
        omega
      rw [hindex, deriv_expIterate_succ, norm_mul]
      calc
        |(expIterate ((1 + m) + 1) z).im|
            =
            |(Complex.exp (expIterate (1 + m) z)).im| := by
              rw [expIterate_succ]
        _ ≤ |(expIterate (1 + m) z).im| *
              ‖Complex.exp (expIterate (1 + m) z)‖ :=
              abs_im_exp_le (expIterate (1 + m) z)
        _ ≤ ‖deriv (expIterate (1 + m)) z‖ *
              ‖Complex.exp (expIterate (1 + m) z)‖ := by
              exact mul_le_mul_of_nonneg_right (ih (by omega)) (norm_nonneg _)
end ExponentialJuliaSetMisiurewicz
