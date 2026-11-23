-- Prove2me | solution 1 for Formalism.FX.rectInt_inv_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:41.526876+00:00
-- url     : https://prove2.me/submissions/31bc81a3-b3ba-4db7-bbe6-9b9437e6b581

import Definitions.Def_Formalism_LFunctionBounds_ExpSumLowerBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Theorems.Thm_Formalism_FX_rectRes_ftc_log
import Theorems.Thm_Formalism_FX_rectRes_log_sub_log_neg_of_im_pos
import Theorems.Thm_Formalism_FX_rectRes_log_sub_log_neg_of_im_neg
import Theorems.Thm_Formalism_FX_rectRes_hasDerivAt_horiz
import Theorems.Thm_Formalism_FX_rectRes_hasDerivAt_vert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.FX
namespace Formalism.FX
theorem _root_.solution (p : ℂ) (x0 x1 y0 y1 : ℝ) (h1 : x0 < p.re) (h2 : p.re < x1)
    (h3 : y0 < p.im) (h4 : p.im < y1) :
    rectInt (fun w => 1 / (w - p)) x0 x1 y0 y1 = 2 * (Real.pi : ℂ) * I := by
  have E1 : ∫ x in x0..x1, 1 / ((x : ℂ) + (y0 : ℂ) * I - p) =
      log ((x1 : ℂ) + (y0 : ℂ) * I - p) - log ((x0 : ℂ) + (y0 : ℂ) * I - p) := by
    have h := rectRes_ftc_log (γ := fun x : ℝ => (x : ℂ) + ((y0 : ℂ) * I - p)) (d := 1)
      (a := x0) (b := x1) (fun t => rectRes_hasDerivAt_horiz _ t)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inr (by intro h'; simp at h'; linarith)))
    simpa only [add_sub_assoc] using h
  have E2 : ∫ x in x0..x1, 1 / ((x : ℂ) + (y1 : ℂ) * I - p) =
      log ((x1 : ℂ) + (y1 : ℂ) * I - p) - log ((x0 : ℂ) + (y1 : ℂ) * I - p) := by
    have h := rectRes_ftc_log (γ := fun x : ℝ => (x : ℂ) + ((y1 : ℂ) * I - p)) (d := 1)
      (a := x0) (b := x1) (fun t => rectRes_hasDerivAt_horiz _ t)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inr (by intro h'; simp at h'; linarith)))
    simpa only [add_sub_assoc] using h
  have E3 : I * ∫ y in y0..y1, 1 / ((x1 : ℂ) + (y : ℂ) * I - p) =
      log ((x1 : ℂ) + (y1 : ℂ) * I - p) - log ((x1 : ℂ) + (y0 : ℂ) * I - p) := by
    have h := rectRes_ftc_log (γ := fun y : ℝ => ((x1 : ℂ) - p) + (y : ℂ) * I) (d := I)
      (a := y0) (b := y1) (fun t => rectRes_hasDerivAt_vert _ t)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inl (by simp <;> linarith)))
    rw [← intervalIntegral.integral_const_mul]
    have e1 : (x1 : ℂ) + (y1 : ℂ) * I - p = ((x1 : ℂ) - p) + (y1 : ℂ) * I := by ring
    have e0 : (x1 : ℂ) + (y0 : ℂ) * I - p = ((x1 : ℂ) - p) + (y0 : ℂ) * I := by ring
    rw [e1, e0, ← h]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    show I * (1 / ((x1 : ℂ) + (y : ℂ) * I - p)) = I / (((x1 : ℂ) - p) + (y : ℂ) * I)
    rw [mul_one_div]
    congr 1
    ring
  have E4 : I * ∫ y in y0..y1, 1 / ((x0 : ℂ) + (y : ℂ) * I - p) =
      log (-((x0 : ℂ) + (y1 : ℂ) * I - p)) - log (-((x0 : ℂ) + (y0 : ℂ) * I - p)) := by
    have h := rectRes_ftc_log (γ := fun y : ℝ => -(((x0 : ℂ) - p) + (y : ℂ) * I)) (d := -I)
      (a := y0) (b := y1) (fun t => (rectRes_hasDerivAt_vert _ t).neg)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inl (by simp <;> linarith)))
    rw [← intervalIntegral.integral_const_mul]
    have e1 : (x0 : ℂ) + (y1 : ℂ) * I - p = ((x0 : ℂ) - p) + (y1 : ℂ) * I := by ring
    have e0 : (x0 : ℂ) + (y0 : ℂ) * I - p = ((x0 : ℂ) - p) + (y0 : ℂ) * I := by ring
    rw [e1, e0, ← h]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    show I * (1 / ((x0 : ℂ) + (y : ℂ) * I - p)) = -I / -(((x0 : ℂ) - p) + (y : ℂ) * I)
    rw [neg_div_neg_eq, mul_one_div]
    congr 1
    ring
  have P1 := rectRes_log_sub_log_neg_of_im_pos (z := (x0 : ℂ) + (y1 : ℂ) * I - p)
    (by simp <;> linarith)
  have P0 := rectRes_log_sub_log_neg_of_im_neg (z := (x0 : ℂ) + (y0 : ℂ) * I - p)
    (by simp <;> linarith)
  unfold rectInt
  beta_reduce
  rw [E1, E2, E3, E4]
  linear_combination P1 - P0
end Formalism.FX
