-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_cube_quintic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:05:57.831012+00:00
-- url     : https://prove2.me/submissions/0691ccd8-bbf8-4913-8b16-d860efe07ad3

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_derivative_real_supporting_parent
import Theorems.Thm_DerivativeChainPrivate_quadrant_phase_forces_nonnegative_im
import Theorems.Thm_DerivativeChainPrivate_rational_inverse_parts
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

theorem inverse_graph_southeast_impossible
    (α₀ α₁ b₀ b₁ A₀ A₁ B₀ B₁ K R I x y r v : ℝ)
    (hα₁ : 0 < α₁) (hα : α₁ < α₀)
    (hx : 0 < x) (hv : 0 < v) (hxr : x ≤ r) (hvy : v ≤ y)
    (hR : 0 ≤ R) (hI : 0 ≤ I)
    (hC₀ : (3 * A₀ - B₀) / 2 ≤ K) (hC₁ : 0 ≤ (3 * A₁ - B₁) / 2)
    (hgap : K < b₀ - b₁)
    (hR₀ : R / x = α₀ * (x ^ 2 - 3 * y ^ 2) - b₀ + A₀)
    (hI₀ : I / y = α₀ * (3 * x ^ 2 - y ^ 2) - b₀ + B₀)
    (hR₁ : R / r = α₁ * (r ^ 2 - 3 * v ^ 2) - b₁ + A₁)
    (hI₁ : I / v = α₁ * (3 * r ^ 2 - v ^ 2) - b₁ + B₁) : False := by
  have hreal := div_le_div_of_nonneg_left hR hx hxr
  have himag := div_le_div_of_nonneg_left hI hv hvy
  rw [hR₀, hR₁] at hreal
  rw [hI₀, hI₁] at himag
  have hsq : v ^ 2 ≤ y ^ 2 := by nlinarith only [hv, hvy]
  have hterm₀ := mul_nonneg (sub_pos.mpr hα).le (sq_nonneg y)
  have hterm₁ := mul_nonneg hα₁.le (sub_nonneg.mpr hsq)
  nlinarith only [hreal, himag, hterm₀, hterm₁, hC₀, hC₁, hgap]



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
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



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







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
theorem solution (β w : ℂ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hwpos : 0 < w.re) (hwim : 0 ≤ w.im)
    (hwX : 7/4 ≤ w.re ^ 2)
    (hwroot : w ^ 4 - 2 * w ^ 2 - 4 * β * w + 8/21 = 0)
    (hwinv : β / w = (1/4 : ℂ) * w ^ 2 - 1/2 + (2/21 : ℂ) / w ^ 2) :
    ∃ z : ℂ,
      z ^ 5 - 10/3 * z ^ 3 - 10 * β * z ^ 2 + 40/21 * z + 16/3 * β = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 5/2 ≤ z.re ^ 2 ∧
      β / z = (1/10 : ℂ) * z ^ 2 - 7/25 + (36/875 : ℂ) / (z ^ 2 - 8/15) := by
  have hwne : w ≠ 0 := by intro h; simp [h] at hwpos
  obtain ⟨hwR,hwI,hwphase,hwD⟩ := rational_inverse_parts β w (1/4) (1/2) (2/21) 0 hwne
    (by simpa using pow_ne_zero 2 hwne) (by push_cast; simpa using hwinv)
  simp only [Complex.ofReal_zero,sub_zero,zero_mul,mul_zero,add_zero] at hwR hwI hwphase hwD
  let W := w.re ^ 2 + w.im ^ 2
  have hW : 1 ≤ W := by dsimp only [W]; nlinarith only [hwX,sq_nonneg w.im]
  have hWpos : 0 < W := by linarith
  have hwD1 : 1 ≤ ‖w ^ 2‖ ^ 2 := by rw [hwD]; change 1 ≤ W ^ 2; nlinarith only [hW]
  have hwDp : 0 < ‖w ^ 2‖ ^ 2 := by linarith
  have hwphasep : 0 < (1/4 : ℝ) - (2/21) / ‖w ^ 2‖ ^ 2 := by
    have hquot : (2/21 : ℝ) / ‖w ^ 2‖ ^ 2 ≤ 2/21 :=
      (div_le_iff₀ hwDp).mpr (by linarith)
    linarith
  have hwzero := (quadrant_phase_forces_nonnegative_im β w _ hR hI hwpos hwphasep hwphase).2
  let p : Polynomial ℂ := X ^ 5 - C (10/3) * X ^ 3 - 10 * C β * X ^ 2 +
    C (40/21) * X + C (16/3) * C β
  have hpdeg : p.natDegree = 5 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w = 0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 5 * hwroot
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hXpre : 7/4 ≤ z.re ^ 2 := by nlinarith only [hwX,hxz,hwpos]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hx
  have hpole : z ^ 2 - (8/15 : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    norm_num [pow_two,Complex.mul_re,Complex.mul_im] at hr hi
    have hm : z.re * z.im = 0 := by nlinarith only [hi]
    have hy := (mul_eq_zero.mp hm).resolve_left hx.ne'
    rw [hy] at hr
    nlinarith only [hr,hXpre]
  have hzroot : z ^ 5 - 10/3 * z ^ 3 - 10 * β * z ^ 2 + 40/21 * z + 16/3 * β = 0 := by
    simpa only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] using hz
  have hzinv : β / z = (1/10 : ℂ) * z ^ 2 - 7/25 + (36/875 : ℂ) / (z ^ 2 - 8/15) := by
    have hform : β / z = (z ^ 4 - 10/3 * z ^ 2 + 40/21) / (10 * (z ^ 2 - 8/15)) := by
      apply (div_eq_div_iff hz0 (mul_ne_zero (by norm_num) hpole)).2
      linear_combination -hzroot
    rw [hform]
    apply (div_eq_iff (mul_ne_zero (by norm_num : (10 : ℂ) ≠ 0) hpole)).2
    calc
      _ = ((1/10 : ℂ) * z ^ 2 - 7/25) * (10 * (z ^ 2 - 8/15)) + (36/875) * 10 := by ring
      _ = ((1/10 : ℂ) * z ^ 2 - 7/25) * (10 * (z ^ 2 - 8/15)) +
          ((36/875) / (z ^ 2 - 8/15) * (z ^ 2 - 8/15)) * 10 := by rw [div_mul_cancel₀ _ hpole]
      _ = _ := by ring
  obtain ⟨hzR,hzI,hzphase,hD⟩ := rational_inverse_parts β z (1/10) (7/25) (36/875) (8/15)
    hz0 (by push_cast; exact hpole) (by push_cast; exact hzinv)
  push_cast at hzR hzI hzphase hD
  let U := z.re ^ 2 + z.im ^ 2
  let D := ‖z ^ 2 - (8/15 : ℂ)‖ ^ 2
  have hU : 7/4 ≤ U := by dsimp only [U]; nlinarith only [hXpre,sq_nonneg z.im]
  have hUc : 1 ≤ U - 8/15 := by linarith
  have hUcp : 0 < U - 8/15 := by linarith
  have hDlow : (U - 8/15) ^ 2 ≤ D := by
    dsimp only [U,D]
    nlinarith only [hD,sq_nonneg z.im]
  have hD1 : 1 ≤ D := by nlinarith only [hDlow,hUc]
  have hDp : 0 < D := by linarith
  have hphasep : 0 < (1/10 : ℝ) - (36/875) / D := by
    have hquot : (36/875 : ℝ) / D ≤ 36/875 := (div_le_iff₀ hDp).mpr (by linarith)
    linarith
  obtain ⟨hzim,_⟩ := quadrant_phase_forces_nonnegative_im β z _ hR hI hx hphasep hzphase
  have himorder : w.im ≤ z.im := by
    by_contra hfail
    have hlt : z.im < w.im := lt_of_not_ge hfail
    by_cases hzero : z.im = 0
    · have hβzero : β.im = 0 := by rw [hzI,hzero,zero_mul]
      have hwzero' := hwzero hβzero
      linarith
    · have hv : 0 < z.im := lt_of_le_of_ne hzim (Ne.symm hzero)
      have hy : 0 < w.im := lt_trans hv hlt
      have hCw : (3 * ((2/21) * W / ‖w ^ 2‖ ^ 2) - (-((2/21) * W / ‖w ^ 2‖ ^ 2))) / 2 ≤ 4/21 := by
        have hid : (3 * ((2/21) * W / ‖w ^ 2‖ ^ 2) - (-((2/21) * W / ‖w ^ 2‖ ^ 2))) / 2 =
            (4/21 : ℝ) / W := by rw [hwD]; change _ = (4/21 : ℝ) / W; field_simp; ring
        rw [hid]
        apply (div_le_iff₀ hWpos).2
        linarith
      have hAz : 0 ≤ (36/875 : ℝ) * (U - 8/15) / D := by positivity
      have hBz : 0 ≤ (36/875 : ℝ) * (U + 8/15) / D := by positivity
      apply inverse_graph_southeast_impossible (1/4) (1/10) (1/2) (7/25)
        ((2/21) * W / ‖w ^ 2‖ ^ 2) ((36/875) * (U-8/15) / D)
        (-((2/21) * W / ‖w ^ 2‖ ^ 2)) (-((36/875) * (U+8/15) / D)) (4/21)
        β.re β.im w.re w.im z.re z.im
        (by norm_num) (by norm_num) hwpos hv hxz hlt.le hR hI hCw
        (by linarith only [hAz,hBz]) (by norm_num)
      · rw [hwR]; dsimp only [W]; field_simp <;> ring
      · rw [hwI]; dsimp only [W]; field_simp <;> ring
      · rw [hzR]; dsimp only [U,D]; field_simp <;> ring
      · rw [hzI]; dsimp only [U,D]; field_simp <;> ring
  have hXcp : 0 < z.re ^ 2 - 8/15 := by linarith
  have hA : (36/875 : ℝ) * (U - 8/15) / D ≤ (36/875) / (z.re ^ 2 - 8/15) := by
    calc
      _ ≤ (36/875) / (U-8/15) := by
        apply (div_le_div_iff₀ hDp hUcp).2
        nlinarith only [mul_le_mul_of_nonneg_left hDlow (show (0 : ℝ) ≤ 36/875 by norm_num)]
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hXcp
        (by dsimp only [U]; nlinarith only [sq_nonneg z.im])
  have hbr : 0 ≤ (1/10 : ℝ) * (z.re ^ 2 - 3 * z.im ^ 2) - 7/25 + (36/875) * (U-8/15) / D := by
    apply nonneg_of_mul_nonneg_right ?_ hx
    simpa only [U,D] using (hzR ▸ hR)
  have hweak : 0 ≤ z.re ^ 2 - 14/5 + (72/175) / (z.re ^ 2 - 8/15) := by
    have hcoeff : (72/175 : ℝ) / (z.re ^ 2 - 8/15) =
        10 * ((36/875) / (z.re ^ 2 - 8/15)) := by ring
    rw [hcoeff]
    nlinarith only [hbr,hA,sq_nonneg z.im]
  have hid : z.re ^ 2 - 14/5 + (72/175) / (z.re ^ 2 - 8/15) =
      ((z.re ^ 2) ^ 2 - 10/3 * z.re ^ 2 + 40/21) / (z.re ^ 2 - 8/15) := by
    apply (eq_div_iff hXcp.ne').2
    calc
      _ = (z.re ^ 2 - 14/5) * (z.re ^ 2 - 8/15) +
          ((72/175) / (z.re ^ 2 - 8/15)) * (z.re ^ 2 - 8/15) := by ring
      _ = (z.re ^ 2 - 14/5) * (z.re ^ 2 - 8/15) + 72/175 := by rw [div_mul_cancel₀ _ hXcp.ne']
      _ = _ := by ring
  rw [hid] at hweak
  have hpoly := (le_div_iff₀ hXcp).mp hweak
  have hX : 5/2 ≤ z.re ^ 2 := by
    by_contra hfail
    have hprod := mul_nonneg (show 0 ≤ z.re ^ 2 - 7/4 by linarith)
      (show 0 ≤ 5/2 - z.re ^ 2 by linarith)
    nlinarith only [hpoly,hprod,lt_of_not_ge hfail]
  exact ⟨z,hzroot,hxz,himorder,hX,hzinv⟩
