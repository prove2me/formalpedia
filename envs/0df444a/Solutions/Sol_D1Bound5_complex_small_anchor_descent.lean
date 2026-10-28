-- Prove2me | solution 1 for D1Bound5.complex_small_anchor_descent
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:15.745844+00:00
-- url     : https://prove2.me/submissions/eb400e56-859d-4dbc-a58c-cd9d1589b6e8

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Theorems.Thm_D1Bound5_exists_sign_root_perturbation
import Theorems.Thm_D1Bound5_exists_small_descent_multiplier

section
namespace D1Bound5



/-- The analytic part of the small-anchor descent. The sole arithmetic
input is the multiplier norm bound, supplied separately from integrality.
The square root sign is chosen by the already proved perturbation lemma. -/
theorem _root_.solution
    (a b z r0 r s : ℂ)
    (h0 : r0^2 = a*b+1) (hr : r^2 = a*z+1) (hs : s^2 = b*z+1)
    (hA : ‖a‖ < 3) (hB : ‖b‖ < 3)
    (hp : 1 ≤ ‖a*b‖) (hZ : 33 ≤ ‖z‖)
    (hhyper : 7 ≤ ‖2*a*b+1‖^2) :
    ‖mutate a b z r0 r s‖ < ‖z‖/5+26 ∨
      ‖mutate a b z r0 r (-s)‖ < ‖z‖/5+26 := by
  obtain ⟨eta, heta, hsmall⟩ := exists_small_descent_multiplier (a*b) r0 h0
    (by simpa only [mul_assoc] using hhyper)
  have hetaN : ‖eta‖^2 = ‖a*b‖ := by rw [← norm_pow, heta]
  have heta1 : 1 ≤ ‖eta‖^2 := by rw [hetaN]; exact hp
  have heta0 : eta ≠ 0 := by
    intro he
    simp only [he, norm_zero, zero_pow (by decide : 2 ≠ 0)] at heta1
    norm_num at heta1
  have hZp : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hZp
  have hAB : ‖a‖+‖b‖ < 6 := by linarith
  have hdiff : (r*s)^2-(eta*z)^2 = (a+b)*z+1 := by
    rw [mul_pow, mul_pow, hr, hs, heta]
    ring
  have herr : ‖(r*s)^2-(eta*z)^2‖ ≤ 7*‖z‖ := by
    rw [hdiff]
    calc
      _ ≤ ‖(a+b)*z‖+‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖a+b‖*‖z‖+1 := by rw [norm_mul, norm_one]
      _ ≤ (‖a‖+‖b‖)*‖z‖+1 :=
        add_le_add (mul_le_mul_of_nonneg_right (norm_add_le a b) (norm_nonneg z)) le_rfl
      _ ≤ 7*‖z‖ := by
        have hh := mul_lt_mul_of_pos_right hAB hZp
        nlinarith only [hh, hZ]
  have hgap : 7*‖z‖ < (1-(0 : ℝ)^2)*‖eta*z‖^2 := by
    rw [norm_mul, mul_pow]
    norm_num
    have hzz : 7*‖z‖ < ‖z‖^2 := by
      nlinarith only [mul_pos hZp (show 0 < ‖z‖-7 by linarith)]
    nlinarith only [hzz, mul_nonneg (sub_nonneg.mpr heta1) (sq_nonneg ‖z‖)]
  obtain ⟨tau, htau, hnear⟩ := exists_sign_root_perturbation (r*s) (eta*z) 0
    (7*‖z‖) (mul_ne_zero heta0 hz0) (by norm_num) (by positivity) herr hgap
  have hdelta : ‖eta‖*‖tau-eta*z‖ < 7 := by
    have hh : ‖z‖*(‖eta‖*‖tau-eta*z‖) < ‖z‖*7 := by
      simpa only [norm_mul, add_zero, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hnear
    by_contra hbad
    have hnonneg : 0 ≤ ‖eta‖*‖tau-eta*z‖-7 :=
      sub_nonneg.mpr (le_of_not_gt hbad)
    nlinarith only [hh, mul_nonneg hZp.le hnonneg]
  have hr0norm : ‖r0‖^2 ≤ 2*‖eta‖^2 := by
    calc
      ‖r0‖^2 = ‖r0^2‖ := (norm_pow r0 2).symm
      _ = ‖a*b+1‖ := by rw [h0]
      _ ≤ ‖a*b‖+1 := by simpa only [norm_one] using norm_add_le (a*b) (1 : ℂ)
      _ ≤ 2*‖eta‖^2 := by rw [hetaN]; nlinarith only [hp]
  have hdelta0 : 0 ≤ ‖eta‖*‖tau-eta*z‖ := by positivity
  have hdeltasq : (‖eta‖*‖tau-eta*z‖)^2 < 49 := by
    nlinarith only [mul_pos (sub_pos.mpr hdelta)
      (add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 7) hdelta0)]
  have hscaled := mul_le_mul_of_nonneg_right hr0norm (sq_nonneg ‖tau-eta*z‖)
  have herror : 2*‖r0‖*‖tau-eta*z‖ < 20 := by
    nlinarith only [hdeltasq, hscaled,
      mul_nonneg (norm_nonneg r0) (norm_nonneg (tau-eta*z)),
      sq_nonneg (‖r0‖*‖tau-eta*z‖-10)]
  have hw : ‖a+b+(2*a*b+1)*z-2*r0*tau‖ < ‖z‖/5+26 := by
    have hid : a+b+(2*a*b+1)*z-2*r0*tau =
        (a+b)+(2*(a*b)+1-2*r0*eta)*z-2*r0*(tau-eta*z) := by ring
    rw [hid]
    calc
      _ ≤ ‖(a+b)+(2*(a*b)+1-2*r0*eta)*z‖+‖2*r0*(tau-eta*z)‖ := norm_sub_le _ _
      _ ≤ (‖a+b‖+‖(2*(a*b)+1-2*r0*eta)*z‖)+‖2*r0*(tau-eta*z)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = ‖a+b‖+‖2*(a*b)+1-2*r0*eta‖*‖z‖+2*‖r0‖*‖tau-eta*z‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_two]
      _ ≤ (‖a‖+‖b‖)+‖2*(a*b)+1-2*r0*eta‖*‖z‖+2*‖r0‖*‖tau-eta*z‖ := by
        linarith only [norm_add_le a b]
      _ < ‖z‖/5+26 := by
        have hmult := mul_lt_mul_of_pos_right hsmall hZp
        nlinarith only [hAB, hmult, herror]
  rcases htau with htau | htau
  · right
    convert hw using 1 <;> rw [htau] <;> unfold mutate <;> congr 1 <;> ring
  · left
    convert hw using 1 <;> rw [htau] <;> unfold mutate <;> congr 1 <;> ring

end D1Bound5
end
