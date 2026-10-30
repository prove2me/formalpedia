-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_quintic_estimates
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:02:59.623313+00:00
-- url     : https://prove2.me/submissions/1e3351b5-51cb-4ea2-bb72-7d4eea27334f

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_quadrant_phase_forces_nonnegative_im
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


theorem solution (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < w.re) (hy : 0 ≤ w.im) (hX : 5/2 ≤ w.re^2)
    (hinv : β/w = (1/10:ℂ)*w^2-41/140+(459/7840:ℂ)/(w^2-17/42)) :
    let U := w.re^2+w.im^2
    let D := ‖w^2-(17/42:ℂ)‖^2
    let A := (459/7840:ℝ)*(U-17/42)/D
    let B := -(459/7840:ℝ)*(U+17/42)/D
    0 ≤ A ∧ A ≤ 3/100 ∧ B ≤ 0 ∧ (3*A-B)/2 ≤ 1/15 ∧
      5/2 ≤ w.re^2-3*w.im^2 ∧
      β.re/w.re = (1/10:ℝ)*(w.re^2-3*w.im^2)-41/140+A ∧
      (0 < w.im → β.im/w.im = (1/10:ℝ)*(3*w.re^2-w.im^2)-41/140+B) ∧
      (β.im=0 → w.im=0) := by
  let U := w.re^2+w.im^2
  let D := ‖w^2-(17/42:ℂ)‖^2
  let A := (459/7840:ℝ)*(U-17/42)/D
  let B := -(459/7840:ℝ)*(U+17/42)/D
  have hU : 5/2 ≤ U := by dsimp [U]; nlinarith [sq_nonneg w.im]
  have hUc : 0 < U-17/42 := by linarith
  have hw : w ≠ 0 := by intro h; simp [h] at hx
  have hpole : w^2-(17/42:ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    norm_num [pow_two,Complex.mul_re,Complex.mul_im] at hr hi
    have hi0 : w.im = 0 := by nlinarith
    nlinarith [hX]
  obtain ⟨hr,hi,hphase,hd⟩ := rational_inverse_parts β w (1/10) (41/140) (459/7840) (17/42)
    hw (by norm_num; exact hpole) (by norm_num; exact hinv)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hr hi hphase hd
  have hDlow : (U-17/42)^2 ≤ D := by dsimp only [U,D]; nlinarith only [hd,sq_nonneg w.im]
  have hDp : 0 < D := lt_of_lt_of_le (sq_pos_of_pos hUc) hDlow
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hAu : A ≤ 3/100 := by
    dsimp only [A]
    apply (div_le_iff₀ hDp).mpr
    nlinarith [sq_nonneg (U-5/2)]
  have hB0 : B ≤ 0 := by dsimp only [B]; apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith
  have hC : (3*A-B)/2 ≤ 1/15 := by
    have he : (3*A-B)/2 = (459/7840:ℝ)*(2*U-17/42)/D := by dsimp [A,B]; ring
    rw [he]
    apply (div_le_iff₀ hDp).mpr
    nlinarith [sq_nonneg (U-5/2)]
  have hRpart : β.re/w.re = (1/10:ℝ)*(w.re^2-3*w.im^2)-41/140+A := by
    rw [hr]
    dsimp only [A,U,D]
    field_simp
  have hW : 5/2 ≤ w.re^2-3*w.im^2 := by
    have hh : 0 ≤ β.re/w.re := div_nonneg hR hx.le
    rw [hRpart] at hh
    linarith only [hh,hAu]
  have hphasepos : 0 < (1/10:ℝ)-(459/7840)/D := by
    have hD1 : 1 < D := by nlinarith
    have hb : (459/7840:ℝ)/D ≤ 459/7840 := by
      apply (div_le_iff₀ hDp).mpr
      linarith
    linarith
  have hzero := (quadrant_phase_forces_nonnegative_im β w _ hR hI hx hphasepos hphase).2
  refine ⟨hA0,hAu,hB0,hC,hW,hRpart,?_,hzero⟩
  intro hypos
  rw [hi]
  field_simp <;> ring
