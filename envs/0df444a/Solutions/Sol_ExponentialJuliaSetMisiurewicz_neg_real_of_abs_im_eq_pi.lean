-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.neg_real_of_abs_im_eq_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:32.406837+00:00
-- url     : https://prove2.me/submissions/19dbefc9-a283-402f-a860-f2be773a839d

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exp_neg_real_of_odd_mul_pi

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {z : ℂ} (h : |z.im| = Real.pi) :
    (Complex.exp z).im = 0 ∧ (Complex.exp z).re < 0 := by
  rcases abs_eq (le_of_lt Real.pi_pos) |>.mp h with h' | h'
  · refine exp_neg_real_of_odd_mul_pi (k := 1) ⟨0, by ring⟩ ?_
    rw [h']; push_cast; ring
  · refine exp_neg_real_of_odd_mul_pi (k := -1) ⟨-1, by ring⟩ ?_
    rw [h']; push_cast; ring
end ExponentialJuliaSetMisiurewicz
