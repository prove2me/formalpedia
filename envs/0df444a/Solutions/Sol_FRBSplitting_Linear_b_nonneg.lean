-- Prove2me | solution 1 for FRBSplitting.Linear.b_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:40:22.000212+00:00
-- url     : https://prove2.me/submissions/422c29a6-d7aa-469b-a8e7-0af7ec8ba78e

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linear_Setting

set_option autoImplicit false
open InnerProductSpace ThreeOpSplitting.Accel
open FRBSplitting.Linear

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (L lam : ℝ)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hlam0 : 0 < lam) (hlam1 : lam < 1 / (2 * L))
    (x : ℕ → H) (xs : H) :
    ∀ k : ℕ, 0 ≤ bSeq B lam x xs k := by
  intro k
  unfold bSeq
  set u := x (k + 1) - xs with hu
  set v := x (k + 1) - x k with hv
  have hlam : 2 * lam * L ≤ 1 := by
    have := (lt_div_iff₀ (by positivity : 0 < 2 * L)).mp hlam1
    nlinarith
  have hCS : |inner ℝ (B (x (k + 1)) - B (x k)) (xs - x (k + 1))| ≤ ‖B (x (k + 1)) - B (x k)‖ * ‖xs - x (k + 1)‖ :=
    abs_real_inner_le_norm _ _
  have hLip := hBL (x (k + 1)) (x k)
  have h2 : ‖xs - x (k + 1)‖ = ‖u‖ := by rw [hu, norm_sub_rev]
  have hnu := norm_nonneg u
  have hnv := norm_nonneg v
  have h3 : |inner ℝ (B (x (k + 1)) - B (x k)) (xs - x (k + 1))| ≤ L * ‖v‖ * ‖u‖ := by
    rw [h2] at hCS
    calc _ ≤ ‖B (x (k + 1)) - B (x k)‖ * ‖u‖ := hCS
      _ ≤ (L * ‖x (k + 1) - x k‖) * ‖u‖ := mul_le_mul_of_nonneg_right hLip hnu
  have h4 := neg_abs_le (inner ℝ (B (x (k + 1)) - B (x k)) (xs - x (k + 1)))
  have h5 : 2 * lam * (L * ‖v‖ * ‖u‖) ≤ ‖v‖ * ‖u‖ := by
    have : 0 ≤ ‖v‖ * ‖u‖ := mul_nonneg hnv hnu
    nlinarith
  have h6 : -(‖v‖ * ‖u‖) ≤ 2 * lam * inner ℝ (B (x (k + 1)) - B (x k)) (xs - x (k + 1)) := by
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 2 * lam)]
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
