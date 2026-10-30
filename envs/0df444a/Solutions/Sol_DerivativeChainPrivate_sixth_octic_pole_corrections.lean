-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_pole_corrections
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:03:19.402474+00:00
-- url     : https://prove2.me/submissions/535f7614-70b7-44c8-a284-4eb43e1dd7e2

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_rational_inverse_parts
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution (z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 4 ≤ z.re^2) :
    let U := z.re^2+z.im^2
    let E := (1071/9680)*z/(z^2-17/33)
    (3/40)/U ≤ E.re/z.re ∧ E.re/z.re ≤ (13/100)/U ∧
      -(17/100)/U ≤ E.im/z.im ∧ E.im/z.im ≤ -(9/100)/U := by
  let U := z.re^2+z.im^2
  let D := ‖z^2-(17/33:ℂ)‖^2
  let E := (1071/9680:ℂ)*z/(z^2-17/33)
  have hU : 4 ≤ U := by dsimp [U]; nlinarith [sq_nonneg z.im]
  have hUp : 0 < U := by linarith
  have hUc : 0 < U-17/33 := by linarith
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hpole : z^2-(17/33:ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    norm_num [pow_two,Complex.mul_re,Complex.mul_im] at hr hi
    nlinarith only [hi,hx,hy]
  obtain ⟨hr,hi,_,hd⟩ := rational_inverse_parts E z 0 0 (1071/9680) (17/33) hz (by norm_num; exact hpole)
    (by dsimp [E]; norm_num; field_simp)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one,zero_mul,sub_zero,zero_add,zero_sub] at hr hi hd
  have hDlo : (U-17/33)^2 ≤ D := by
    dsimp only [D,U]
    nlinarith only [hd,sq_nonneg z.im]
  have hDhi : D ≤ (U+17/33)^2 := by
    dsimp only [D,U]
    nlinarith only [hd,sq_nonneg z.re]
  have hDp : 0 < D := lt_of_lt_of_le (sq_pos_of_pos hUc) hDlo
  have hAr : E.re/z.re = (1071/9680:ℝ)*(U-17/33)/D := by
    rw [hr]
    dsimp [U,D]
    field_simp
  have hBi : E.im/z.im = -(1071/9680:ℝ)*(U+17/33)/D := by
    rw [hi]
    dsimp [U,D]
    field_simp <;> ring
  have hAlo : (3/40:ℝ)/U ≤ (1071/9680)*(U-17/33)/D := by
    apply (div_le_div_iff₀ hUp hDp).mpr
    nlinarith [sq_nonneg (U-4)]
  have hAhi : (1071/9680:ℝ)*(U-17/33)/D ≤ (13/100)/U := by
    apply (div_le_div_iff₀ hDp hUp).mpr
    nlinarith [sq_nonneg (U-4)]
  have hBlo : (9/100:ℝ)/U ≤ (1071/9680)*(U+17/33)/D := by
    apply (div_le_div_iff₀ hUp hDp).mpr
    nlinarith [sq_nonneg (U-4)]
  have hBhi : (1071/9680:ℝ)*(U+17/33)/D ≤ (17/100)/U := by
    apply (div_le_div_iff₀ hDp hUp).mpr
    nlinarith [sq_nonneg (U-4)]
  change (3/40:ℝ)/U ≤ E.re/z.re ∧ _
  rw [hAr,hBi]
  simp only [neg_mul,neg_div]
  exact ⟨hAlo,hAhi,by linarith,by linarith⟩
