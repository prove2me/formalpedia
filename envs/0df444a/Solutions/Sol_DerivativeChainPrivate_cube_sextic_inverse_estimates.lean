-- Prove2me | solution 1 for DerivativeChainPrivate.cube_sextic_inverse_estimates
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:11:08.825005+00:00
-- url     : https://prove2.me/submissions/1ee1ea52-8cb8-4e87-a012-af8accb51901

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_cube_radical_real_remainder_bounds
import Theorems.Thm_DerivativeChainPrivate_cubic_graph_coordinate_parts
import Theorems.Thm_DerivativeChainPrivate_quadrant_phase_forces_nonnegative_im
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate













end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem near_one_square_root_control (t s : ℂ) (hsq : s ^ 2 = t)
    (hs : 0 < s.re) (ht : ‖t - 1‖ ≤ 1 / 15) :
    ‖s - 1‖ ≤ 1 / 15 ∧ 9 / 10 ≤ s.re ∧
      3 ≤ ‖s + 1‖ ^ 2 ∧ ‖s + 1‖ ≤ 21 / 10 ∧
      2 / 5 ≤ ((s + 1)⁻¹).re ∧ ((s + 1)⁻¹).re ≤ 3 / 5 ∧ ‖(s + 1)⁻¹‖ ≤ 3 / 5 := by
  have hnorm : 1 ≤ ‖s + 1‖ := by
    have h := Complex.re_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have hnormpos : 0 < ‖s + 1‖ := by linarith
  have hfactor : ‖s - 1‖ * ‖s + 1‖ = ‖t - 1‖ := by
    rw [← norm_mul]
    congr 1
    calc
      _ = s ^ 2 - 1 := by ring
      _ = t - 1 := by rw [hsq]
  have hclose : ‖s - 1‖ ≤ 1 / 15 :=
    (le_mul_of_one_le_right (norm_nonneg _) hnorm).trans (hfactor.le.trans ht)
  have hrep : 9 / 10 ≤ s.re := by
    have h := Complex.abs_re_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re] at h
    have hl := (abs_le.mp (h.trans hclose)).1
    linarith
  have hnormlower : 19 / 10 ≤ ‖s + 1‖ := by
    have h := Complex.re_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have hnormupper : ‖s + 1‖ ≤ 21 / 10 := by
    have h : ‖s + 1‖ ≤ ‖s - 1‖ + 2 := by
      convert! norm_add_le (s - 1) (2 : ℂ) using 1 <;> norm_num <;> ring
    linarith
  have hnorminv : ‖(s + 1)⁻¹‖ ≤ 3 / 5 := by
    rw [norm_inv]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hnormpos).2
    linarith
  have hrelower : 2 / 5 ≤ ((s + 1)⁻¹).re := by
    rw [Complex.inv_re, ← Complex.sq_norm]
    apply (le_div_iff₀ (sq_pos_of_pos hnormpos)).2
    simp only [Complex.add_re, Complex.one_re]
    nlinarith only [hnormupper, hnormpos, hrep]
  exact ⟨hclose, hrep, by nlinarith only [hnormlower, hnormpos],
    hnormupper, hrelower, (Complex.re_le_norm _).trans hnorminv, hnorminv⟩



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cube_radicand_close (z : ℂ) (hx : 5 / 2 ≤ z.re ^ 2) :
    ‖(1 + (1 / 6 : ℂ) / z ^ 2) - 1‖ ≤ 1 / 15 := by
  have hU : 5 / 2 ≤ ‖z‖ ^ 2 := by
    have h := Complex.sq_norm_sub_sq_re z
    nlinarith only [h,hx,sq_nonneg z.im]
  have hn : 0 < ‖z‖ ^ 2 := by linarith
  rw [add_sub_cancel_left, norm_div, norm_pow]
  norm_num
  apply (div_le_iff₀ hn).2
  linarith

theorem exists_positive_re_square_root (t : ℂ) (ht : 0 < t.re) :
    ∃ s : ℂ, s ^ 2 = t ∧ 0 < s.re := by
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq t (show 0 < 2 by norm_num)
  have hsre : s.re ≠ 0 := by
    intro h
    have heq := congrArg Complex.re hs
    simp only [pow_two,Complex.mul_re,h,zero_mul,zero_sub] at heq
    nlinarith only [heq,ht,sq_nonneg s.im]
  rcases lt_or_gt_of_ne hsre with hn | hp
  · refine ⟨-s,?_,?_⟩
    · simpa only [neg_sq] using hs
    · simpa only [Complex.neg_re] using neg_pos.mpr hn
  · exact ⟨s,hs,hp⟩

theorem cube_radicand_positive_square_root (z : ℂ) (hx : 5 / 2 ≤ z.re ^ 2) :
    ∃ s : ℂ, s ^ 2 = 1 + (1 / 6 : ℂ) / z ^ 2 ∧ 0 < s.re := by
  apply exists_positive_re_square_root
  have hc := cube_radicand_close z hx
  have hr := Complex.abs_re_le_norm ((1 + (1 / 6 : ℂ) / z ^ 2) - 1)
  have hl := (abs_le.mp (hr.trans hc)).1
  simp only [Complex.sub_re,Complex.one_re] at hl
  linarith

theorem cube_radical_imaginary_relation (z s : ℂ) (hz : z ≠ 0)
    (hsq : s ^ 2 = 1 + (1 / 6 : ℂ) / z ^ 2) :
    6 * s.re * (z.re ^ 2 + z.im ^ 2) ^ 2 * ‖s + 1‖ ^ 2 * ((s + 1)⁻¹).im = z.re * z.im := by
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hIm := congrArg Complex.im hsq
  simp only [Complex.add_im,Complex.one_im,zero_add,Complex.div_im,
    ← Complex.sq_norm,norm_pow] at hIm
  norm_num [pow_two,Complex.mul_im,Complex.mul_re] at hIm
  have hsp : s + 1 ≠ 0 := by
    intro heq
    have hs : s = -1 := eq_neg_of_add_eq_zero_left heq
    rw [hs] at hsq
    norm_num at hsq
    exact hz (by simpa only [pow_eq_zero_iff (by norm_num : 2 ≠ 0)] using hsq)
  have hDn : ‖s + 1‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hsp)
  rw [Complex.inv_im, ← Complex.sq_norm]
  simp only [Complex.add_im,Complex.one_im,add_zero]
  have hprod : 6 * s.re * ‖z‖ ^ 4 * s.im = -(z.re * z.im) := by
    have hn4 : ‖z‖ ^ 4 ≠ 0 := pow_ne_zero 4 (norm_ne_zero_iff.mpr hz)
    field_simp at hIm
    nlinarith only [hIm]
  rw [Complex.sq_norm,Complex.normSq_apply] at hn
  have hzNorm : (z.re ^ 2 + z.im ^ 2) ^ 2 = ‖z‖ ^ 4 := by
    rw [show ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 by ring,Complex.sq_norm,Complex.normSq_apply]
    ring
  rw [hzNorm]
  field_simp [hDn]
  nlinarith only [hprod]

theorem cube_radical_remainder_bounds (z s : ℂ) (hx : 0 < z.re)
    (hy : z.im ≠ 0) (hX : 5 / 2 ≤ z.re ^ 2) (hs : 0 < s.re)
    (hsq : s ^ 2 = 1 + (1 / 6 : ℂ) / z ^ 2) :
    let T := (s + 1)⁻¹
    let E := ((Real.sqrt 2 / 336 : ℝ) : ℂ) * (16 * T + T ^ 2) / z
    0 ≤ E.re / z.re ∧ E.re / z.re ≤ 1 / 50 ∧
      -(1 / 50) ≤ E.im / z.im ∧ E.im / z.im ≤ 0 ∧
      0 ≤ (3 * (E.re / z.re) - E.im / z.im) / 2 ∧
      (3 * (E.re / z.re) - E.im / z.im) / 2 ≤ 1 / 25 := by
  let T := (s + 1)⁻¹
  let U := z.re ^ 2 + z.im ^ 2
  let E := ((Real.sqrt 2 / 336 : ℝ) : ℂ) * (16 * T + T ^ 2) / z
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  have hU : 5 / 2 ≤ U := by dsimp only [U]; nlinarith only [hX,sq_nonneg z.im]
  have hUpos : 0 < U := by linarith
  have hUnorm : ‖z‖ ^ 2 = U := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    dsimp only [U]
    ring
  obtain ⟨_,hp,hD,_,ha,ha',htnorm⟩ := near_one_square_root_control _ s hsq hs
    (cube_radicand_close z hX)
  have hnormT := Complex.sq_norm T
  rw [Complex.normSq_apply] at hnormT
  have hab : T.re ^ 2 + T.im ^ 2 ≤ (3 / 5 : ℝ) ^ 2 := by
    nlinarith only [hnormT,htnorm,norm_nonneg T]
  have hrr : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg 2]
  have hbound := cube_radical_real_remainder_bounds z.re z.im s.re (‖s + 1‖ ^ 2)
    T.re T.im (Real.sqrt 2) hx hy hU hp hD ha ha' hab (Real.sqrt_nonneg 2) hrr
    (cube_radical_imaginary_relation z s hz hsq)
  have hA : E.re / z.re = Real.sqrt 2 / (336 * U) *
      (16 * T.re + T.re ^ 2 - T.im ^ 2 + (z.im / z.re) * (T.im * (16 + 2 * T.re))) := by
    dsimp only [E]
    rw [Complex.div_re,←Complex.sq_norm,hUnorm]
    norm_num [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,pow_two]
    field_simp
    ring
  have hB : E.im / z.im = Real.sqrt 2 / (336 * U) *
      ((z.re / z.im) * (T.im * (16 + 2 * T.re)) - (16 * T.re + T.re ^ 2 - T.im ^ 2)) := by
    dsimp only [E]
    rw [Complex.div_im,←Complex.sq_norm,hUnorm]
    norm_num [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,pow_two]
    field_simp
    ring
  change 0 ≤ E.re / z.re ∧ _
  rw [hA,hB]
  exact hbound

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cube_sextic_algebraic_gaps :
    let r := Real.sqrt 2
    let αm := (5 - 3*r)/14
    let αp := (5 + 3*r)/14
    let bm := (32 - 15*r)/56
    let bp := (32 + 15*r)/56
    1/28 < αm ∧ αm < 1/10 ∧ 3/5 < αp ∧ bp < 1 ∧
      1/25 < bm - 1/7 ∧ 1/12 < 7/25 - bm ∧ 0 < bp - 1/7 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg 2
  have hlo : 7/5 < Real.sqrt 2 := by nlinarith only [hs,hn]
  have hhi : Real.sqrt 2 < 29/20 := by nlinarith only [hs,hn]
  dsimp only
  exact ⟨by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith⟩

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cube_radical_inverse_identity (z s r : ℂ) (hz : z ≠ 0) (hs : s + 1 ≠ 0)
    (hsq : s ^ 2 = 1 + (1/6 : ℂ) / z ^ 2) :
    (10*z^2-16-6*r*(z^2-4/3)*s)/28 =
      (5-3*r)/14*z^2-(32-15*r)/56 +
        (((r/336)*(16*(s+1)⁻¹+((s+1)⁻¹)^2)/z)/z) := by
  have hprod : 6 * z ^ 2 * (s-1) * (s+1) = 1 := by
    field_simp at hsq
    linear_combination hsq
  have hfirst : z ^ 2 * (s-1) = 1 / (6*(s+1)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hs)).2
    linear_combination hprod
  have hdiff : s-1 = 1/(6*z^2*(s+1)) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz)) hs)).2
    linear_combination hprod
  have hG : (10*z^2-16-6*r*(z^2-4/3)*s)/28 - (5-3*r)/14*z^2 + (32-15*r)/56 =
      (r/56)*(s-1)*(16+1/(s+1)) := by
    calc
      _ = (3*r/14)*(-z^2*(s-1)+(4/3)*s-5/4) := by ring
      _ = (3*r/14)*(-1/(6*(s+1))+(4/3)*s-5/4) := by rw [neg_mul,hfirst]; ring
      _ = _ := by field_simp; ring
  calc
    _ = (5-3*r)/14*z^2-(32-15*r)/56+(r/56)*(s-1)*(16+1/(s+1)) := by
      linear_combination hG
    _ = _ := by rw [hdiff]; field_simp; ring

theorem cube_sextic_inverse_split (β z s r : ℂ) (hz : z ≠ 0) (hr : r ^ 2 = 2)
    (hsq : s ^ 2 = 1 + (1/6 : ℂ) / z ^ 2)
    (hroot : z ^ 6 - 5*z^4 - 20*β*z^3 + 40/7*z^2 + 32*β*z - 16/21 + 28*β^2 = 0) :
    β / z = (10*z^2-16-6*r*(z^2-4/3)*s)/28 ∨
      β / z = (10*z^2-16+6*r*(z^2-4/3)*s)/28 := by
  have hint : 21*z^6-105*z^4-420*β*z^3+120*z^2+672*β*z-16+588*β^2 = 0 := by
    linear_combination 21*hroot
  have hid : (3*z^2)*((28*(β/z)-(10*z^2-16))^2-
      72*(z^2-4/3)^2*(1+(1/6 : ℂ)/z^2)) =
      4*(21*z^6-105*z^4-420*β*z^3+120*z^2+672*β*z-16+588*β^2) := by
    field_simp
    ring
  have hdisc : (28*(β/z)-(10*z^2-16))^2-
      72*(z^2-4/3)^2*(1+(1/6 : ℂ)/z^2) = 0 := by
    apply (mul_eq_zero.mp (show (3*z^2)*_ = 0 by rw [hid,hint,mul_zero])).resolve_left
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hz)
  have hB : (6*r*(z^2-4/3)*s)^2 = 72*(z^2-4/3)^2*(1+(1/6 : ℂ)/z^2) := by
    calc
      _ = 36*r^2*(z^2-4/3)^2*s^2 := by ring
      _ = _ := by rw [hr,hsq]; ring
  have hfactor : (28*(β/z)-(10*z^2-16)-6*r*(z^2-4/3)*s) *
      (28*(β/z)-(10*z^2-16)+6*r*(z^2-4/3)*s) = 0 := by
    calc
      _ = (28*(β/z)-(10*z^2-16))^2-(6*r*(z^2-4/3)*s)^2 := by ring
      _ = 0 := by rw [hB]; exact hdisc
  rcases mul_eq_zero.mp hfactor with hplus | hminus
  · right
    linear_combination (1/28 : ℂ)*hplus
  · left
    linear_combination (1/28 : ℂ)*hminus

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



theorem quotient_imaginary_identity (z e : ℂ) (hx : z.re ≠ 0) (hy : z.im ≠ 0) :
    (e/z).im/(2*z.re*z.im) = (e.im/z.im-e.re/z.re)/(2*(z.re^2+z.im^2)) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  have hD : Complex.normSq z ≠ 0 := by
    rw [← Complex.sq_norm]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  rw [Complex.div_im]
  simp only [Complex.normSq_apply]
  have hsum : z.re*z.re+z.im*z.im ≠ 0 := by simpa only [Complex.normSq_apply] using hD
  field_simp

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cube_radical_quotient_imaginary_bounds (z s : ℂ) (hx : 0 < z.re)
    (hy : z.im ≠ 0) (hX : 5/2 ≤ z.re^2) (hs : 0 < s.re)
    (hsq : s^2 = 1+(1/6 : ℂ)/z^2) :
    let T := (s+1)⁻¹
    let E := ((Real.sqrt 2/336 : ℝ) : ℂ)*(16*T+T^2)/z;
    -(1/125) ≤ (E/z).im/(2*z.re*z.im) ∧ (E/z).im/(2*z.re*z.im) ≤ 0 := by
  obtain ⟨hA,hA',hB,hB',_,_⟩ := cube_radical_remainder_bounds z s hx hy hX hs hsq
  dsimp only
  rw [quotient_imaginary_identity z _ hx.ne' hy]
  have hU : 5/2 ≤ z.re^2+z.im^2 := by nlinarith only [hX,sq_nonneg z.im]
  have hUp : 0 < 2*(z.re^2+z.im^2) := by linarith
  constructor
  · apply (le_div_iff₀ hUp).2
    linarith only [hA',hB,hU]
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hA,hB']) hUp.le

theorem cube_radical_graph_phase (β z s : ℂ) (α b σ : ℝ)
    (hx : 0 < z.re) (hX : 5/2 ≤ z.re^2) (hs : 0 < s.re)
    (hsq : s^2 = 1+(1/6 : ℂ)/z^2) (hα : 1/125 < α)
    (hσ : σ = 1 ∨ σ = -1) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hβ : β/z = (α : ℂ)*z^2-(b : ℂ)+
      (σ : ℂ)*(((Real.sqrt 2/336 : ℝ) : ℂ)*(16*(s+1)⁻¹+((s+1)⁻¹)^2)/z)/z) :
    0 ≤ z.im ∧ (β.im = 0 → z.im = 0) := by
  by_cases hy : z.im = 0
  · exact ⟨hy.ge,fun _ => hy⟩
  let E := ((Real.sqrt 2/336 : ℝ) : ℂ)*(16*(s+1)⁻¹+((s+1)⁻¹)^2)/z
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  obtain ⟨hlo,hhi⟩ := cube_radical_quotient_imaginary_bounds z s hx hy hX hs hsq
  have hk : 0 < α+σ*((E/z).im/(2*z.re*z.im)) := by
    rcases hσ with h | h <;> rw [h] <;> dsimp only [E] <;> linarith
  obtain ⟨_,_,hphase⟩ := cubic_graph_coordinate_parts β z ((σ : ℂ)*E) α b hz hβ
  have hscaled : (((σ : ℂ)*E)/z).im = σ*(E/z).im := by
    rw [mul_div_assoc,Complex.mul_im]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  rw [hscaled] at hphase
  apply quadrant_phase_forces_nonnegative_im β z _ hR hI hx hk
  rw [hphase]
  field_simp

theorem cube_radical_real_on_real (z s : ℂ) (hx : 0 < z.re) (hX : 5/2 ≤ z.re^2)
    (hy : z.im = 0) (hs : 0 < s.re) (hsq : s^2 = 1+(1/6 : ℂ)/z^2) :
    (((Real.sqrt 2/336 : ℝ) : ℂ)*(16*(s+1)⁻¹+((s+1)⁻¹)^2)/z).im = 0 := by
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  obtain ⟨_,_,hD,_,_,_,_⟩ := near_one_square_root_control _ s hsq hs (cube_radicand_close z hX)
  have hDp : 0 < ‖s+1‖^2 := by linarith
  have hkey := cube_radical_imaginary_relation z s hz hsq
  rw [hy,mul_zero] at hkey
  have hTim : ((s+1)⁻¹).im = 0 :=
    (mul_eq_zero.mp hkey).resolve_left (ne_of_gt (by positivity))
  norm_num [Complex.div_im,Complex.mul_im,Complex.mul_re,Complex.add_im,Complex.add_re,
    hTim,hy,pow_two]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



open DerivativeChainPrivate in
theorem solution (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < z.re) (hX : 5/2 ≤ z.re^2)
    (hroot : z^6-5*z^4-20*β*z^3+40/7*z^2+32*β*z-16/21+28*β^2 = 0) :
    ∃ (α b : ℝ) (e : ℂ),
      1/28 < α ∧ 1/25 < b-1/7 ∧ β/z = (α : ℂ)*z^2-(b : ℂ)+e/z ∧
      0 ≤ z.im ∧ (β.im = 0 → z.im = 0) ∧ (z.im = 0 → β.im = 0) ∧
      (z.im ≠ 0 → (3*(e.re/z.re)-e.im/z.im)/2 ≤ 1/25) ∧
      ((α < 1/10 ∧ 1/12 < 7/25-b ∧ (z.im ≠ 0 → 0 ≤ (3*(e.re/z.re)-e.im/z.im)/2)) ∨
        (3/5 < α ∧ b < 1 ∧ (z.im ≠ 0 → -(1/50) ≤ e.re/z.re))) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  obtain ⟨s,hsq,hs⟩ := cube_radicand_positive_square_root z hX
  have hsp : s+1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
    linarith
  let αm := (5-3*Real.sqrt 2)/14
  let αp := (5+3*Real.sqrt 2)/14
  let bm := (32-15*Real.sqrt 2)/56
  let bp := (32+15*Real.sqrt 2)/56
  let E := ((Real.sqrt 2/336 : ℝ) : ℂ)*(16*(s+1)⁻¹+((s+1)⁻¹)^2)/z
  obtain ⟨hαm,hαm',hαp,hbp,hbm,hbm',_⟩ := cube_sextic_algebraic_gaps
  have hbpgap : 1/25 < bp-1/7 := by dsimp only [bp]; linarith [Real.sqrt_nonneg 2]
  have hr : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  have hminus : (10*z^2-16-6*(Real.sqrt 2 : ℂ)*(z^2-4/3)*s)/28 =
      (αm : ℂ)*z^2-(bm : ℂ)+E/z := by
    convert! cube_radical_inverse_identity z s (Real.sqrt 2 : ℂ) hz hsp hsq using 1 <;>
      try dsimp only [αm,bm,E] <;> push_cast <;> ring
  have hplus : (10*z^2-16+6*(Real.sqrt 2 : ℂ)*(z^2-4/3)*s)/28 =
      (αp : ℂ)*z^2-(bp : ℂ)+(-E)/z := by
    calc
      _ = (5/7 : ℂ)*z^2-8/7-(10*z^2-16-6*(Real.sqrt 2 : ℂ)*(z^2-4/3)*s)/28 := by ring
      _ = _ := by rw [hminus]; dsimp only [αm,bm,αp,bp]; push_cast; ring
  obtain ⟨α,b,σ,hα,hb,hσ,hgraph,hcases⟩ : ∃ (α b σ : ℝ),
      1/28 < α ∧ 1/25 < b-1/7 ∧ (σ = 1 ∨ σ = -1) ∧
      β/z = (α : ℂ)*z^2-(b : ℂ)+(σ : ℂ)*E/z ∧
      ((σ = 1 ∧ α < 1/10 ∧ 1/12 < 7/25-b) ∨ (σ = -1 ∧ 3/5 < α ∧ b < 1)) := by
    rcases cube_sextic_inverse_split β z s (Real.sqrt 2 : ℂ) hz hr hsq hroot with hm | hp
    · rw [hminus] at hm
      exact ⟨αm,bm,1,hαm,hbm,Or.inl rfl,by simpa using hm,Or.inl ⟨rfl,hαm',hbm'⟩⟩
    · rw [hplus] at hp
      exact ⟨αp,bp,-1,by dsimp only [αp]; linarith only [hαp],hbpgap,Or.inr rfl,
        by simpa using hp,Or.inr ⟨rfl,hαp,hbp⟩⟩
  let e := (σ : ℂ)*E
  have hphase := cube_radical_graph_phase β z s α b σ hx hX hs hsq (by linarith) hσ hR hI hgraph
  obtain ⟨_,hImag,_⟩ := cubic_graph_coordinate_parts β z e α b hz hgraph
  have hAre : e.re/z.re = σ*(E.re/z.re) := by
    dsimp only [e]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  have hBim : e.im/z.im = σ*(E.im/z.im) := by
    dsimp only [e]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    ring
  have hC : (3*(e.re/z.re)-e.im/z.im)/2 = σ*((3*(E.re/z.re)-E.im/z.im)/2) := by
    rw [hAre,hBim]
    ring
  refine ⟨α,b,e,hα,hb,hgraph,hphase.1,hphase.2,?_,?_,?_⟩
  · intro hy
    have hE : E.im = 0 := cube_radical_real_on_real z s hx hX hy hs hsq
    rw [hImag,hy,zero_mul,zero_add]
    dsimp only [e]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,hE,mul_zero,zero_mul,add_zero]
  · intro hy
    obtain ⟨_,_,_,_,hlo,hhi⟩ := cube_radical_remainder_bounds z s hx hy hX hs hsq
    change 0 ≤ (3*(E.re/z.re)-E.im/z.im)/2 at hlo
    change (3*(E.re/z.re)-E.im/z.im)/2 ≤ 1/25 at hhi
    rw [hC]
    rcases hσ with h | h <;> rw [h] <;> linarith only [hlo,hhi]
  · rcases hcases with ⟨hσ₁,hα₁,hb₁⟩ | ⟨hσ₁,hα₁,hb₁⟩
    · left
      refine ⟨hα₁,hb₁,?_⟩
      intro hy
      obtain ⟨_,_,_,_,hlo,_⟩ := cube_radical_remainder_bounds z s hx hy hX hs hsq
      rw [hC,hσ₁,one_mul]
      exact hlo
    · right
      refine ⟨hα₁,hb₁,?_⟩
      intro hy
      obtain ⟨_,hhi,_,_,_,_⟩ := cube_radical_remainder_bounds z s hx hy hX hs hsq
      change E.re/z.re ≤ 1/50 at hhi
      rw [hAre,hσ₁,neg_one_mul]
      linarith only [hhi]
