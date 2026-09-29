-- Prove2me | solution 1 for Freiman.form_reduction_algebra
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:14:53.888299+00:00
-- url     : https://prove2.me/submissions/24fb905e-0484-48b2-8c21-faad41bf7721

import Definitions.Def_Freiman_reducedForms
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option maxHeartbeats 800000

open Freiman

theorem solution (A B C r s : ℝ) (a b c d : ℤ) (α β : ℝ) (hd : 0 < B^2-4*A*C) (hm : 0 < quadraticMinimum A B C) (hA : A ≠ 0) (hfactor : ∀ p q : ℤ, quadraticValue A B C p q = A*((p:ℝ)-r*(q:ℝ))*((p:ℝ)-s*(q:ℝ))) (hdet : formUnimodular a b c d) (hα : 1 < α) (hβ : 0 < β) (hβ1 : β < 1) (hcα : (c:ℝ)*α+(d:ℝ) ≠ 0) (hcβ : -(c:ℝ)*β+(d:ℝ) ≠ 0) (hr : r=((a:ℝ)*α+(b:ℝ))/((c:ℝ)*α+(d:ℝ))) (hs : s=(-(a:ℝ)*β+(b:ℝ))/(-(c:ℝ)*β+(d:ℝ))) (hmin : quadraticMinimum (transformedA A B C a b c d) (transformedB A B C a b c d) (transformedC A B C a b c d) = quadraticMinimum A B C) (hdisc : (transformedB A B C a b c d)^2-4*transformedA A B C a b c d*transformedC A B C a b c d=B^2-4*A*C) (hscale : ∀ k : ℝ, k ≠ 0 → quadraticMinimum (k*reducedA α β) (k*reducedB α β) (k*reducedC α β)=|k| * reducedMinimum α β) :
    0 < reducedMinimum α β ∧ Real.sqrt (B^2-4*A*C) / quadraticMinimum A B C = 1 / reducedMinimum α β := by
  have hab : 0 < α+β := by linarith
  have hab0 : α+β ≠ 0 := ne_of_gt hab
  have hC : C = A*r*s := by
    have h := hfactor 0 1
    norm_num [quadraticValue] at h
    nlinarith only [h]
  have hB : B = -A*(r+s) := by
    have h := hfactor 1 1
    norm_num [quadraticValue] at h
    nlinarith only [h, hC]
  have hrlinear : (b:ℝ)-r*(d:ℝ) = -((a:ℝ)-r*(c:ℝ))*α := by
    have h := (eq_div_iff hcα).mp hr
    nlinarith only [h]
  have hslinear : (b:ℝ)-s*(d:ℝ) = ((a:ℝ)-s*(c:ℝ))*β := by
    have h := (eq_div_iff hcβ).mp hs
    nlinarith only [h]
  let K : ℝ := A*((a:ℝ)-r*(c:ℝ))*((a:ℝ)-s*(c:ℝ))
  let k : ℝ := K*(α+β)
  have hTA : transformedA A B C a b c d = K := hfactor a c
  have hTB : transformedB A B C a b c d = K*(β-α) := by
    calc
      transformedB A B C a b c d =
          A*(((a:ℝ)-r*(c:ℝ))*((b:ℝ)-s*(d:ℝ)) +
             ((b:ℝ)-r*(d:ℝ))*((a:ℝ)-s*(c:ℝ))) := by
        dsimp [transformedB]
        rw [hB, hC]
        ring
      _ = _ := by
        rw [hrlinear, hslinear]
        dsimp only [K]
        ring
  have hTC : transformedC A B C a b c d = -K*α*β := by
    calc
      transformedC A B C a b c d =
          A*((b:ℝ)-r*(d:ℝ))*((b:ℝ)-s*(d:ℝ)) := hfactor b d
      _ = _ := by
        rw [hrlinear, hslinear]
        dsimp only [K]
        ring
  have hkdisc : B^2-4*A*C = k^2 := by
    calc
      B^2-4*A*C = (transformedB A B C a b c d)^2 -
          4*transformedA A B C a b c d*transformedC A B C a b c d := hdisc.symm
      _ = k^2 := by
        rw [hTA, hTB, hTC]
        dsimp only [k]
        ring
  have hk : k ≠ 0 := by
    intro hz
    rw [hz] at hkdisc
    nlinarith only [hkdisc, hd]
  have hscaledA : transformedA A B C a b c d = k*reducedA α β := by
    rw [hTA]
    dsimp only [k, reducedA]
    field_simp
  have hscaledB : transformedB A B C a b c d = k*reducedB α β := by
    rw [hTB]
    dsimp only [k, reducedB]
    field_simp
  have hscaledC : transformedC A B C a b c d = k*reducedC α β := by
    rw [hTC]
    dsimp only [k, reducedC]
    field_simp
  have hminimum : quadraticMinimum A B C = |k| * reducedMinimum α β := by
    rw [← hmin, hscaledA, hscaledB, hscaledC]
    exact hscale k hk
  have hredpos : 0 < reducedMinimum α β := by
    have hprodpos : 0 < |k| * reducedMinimum α β := by rw [← hminimum]; exact hm
    exact (mul_pos_iff_of_pos_left (abs_pos.mpr hk)).mp hprodpos
  refine ⟨hredpos, ?_⟩
  rw [hkdisc, Real.sqrt_sq_eq_abs, hminimum, div_mul_eq_div_div,
    div_self (abs_ne_zero.mpr hk)]

