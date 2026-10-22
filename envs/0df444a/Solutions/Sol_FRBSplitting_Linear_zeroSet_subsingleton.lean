-- Prove2me | solution 1 for FRBSplitting.Linear.zeroSet_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:40:20.663308+00:00
-- url     : https://prove2.me/submissions/09f23208-0896-4dfd-a92a-6dc5a456ca0e

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linear_Setting

set_option autoImplicit false
open InnerProductSpace ThreeOpSplitting.Accel
open FRBSplitting.Linear

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (B : H → H) (m : ℝ)
    (hm : 0 < m) (hAs : IsStronglyMonotoneOp m A)
    (hBm : IsMonotoneFun B) :
    (FRBSplitting.Weak.zeroSet A B).Subsingleton := by
  intro x hx y hy
  have h1 := hAs x y (-B x) (-B y) hx hy
  have h2 := hBm x y
  have e : ⟪x - y, -B x - -B y⟫_ℝ = -⟪x - y, B x - B y⟫_ℝ := by
    rw [← inner_neg_right]; congr 1; abel
  rw [e] at h1
  have h3 : m * ‖x - y‖ ^ 2 ≤ 0 := by linarith
  have h4 : ‖x - y‖ ^ 2 ≤ 0 := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  have h5 : ‖x - y‖ = 0 := by
    have := sq_nonneg ‖x - y‖
    nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h5)
