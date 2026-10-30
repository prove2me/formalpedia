-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_cube_sextic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:14:30.838693+00:00
-- url     : https://prove2.me/submissions/88851ce7-e800-48aa-9654-96797f289858

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_cube_sextic_inverse_estimates
import Theorems.Thm_DerivativeChainPrivate_cubic_graph_coordinate_parts
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

theorem fast_inverse_southeast_impossible (R x y r v α b A₀ A₁ : ℝ)
    (hR : 0 ≤ R) (hx : 0 < x) (hv : 0 ≤ v) (hxr : x ≤ r) (hvy : v ≤ y)
    (hWedge : 5/2 ≤ x^2-3*y^2) (hα : 3/5 < α) (hb : b < 1)
    (hA₀ : A₀ ≤ 1/40) (hA₁ : -(1/50) ≤ A₁)
    (hR₀ : R/x = (1/10)*(x^2-3*y^2)-7/25+A₀)
    (hR₁ : R/r = α*(r^2-3*v^2)-b+A₁) : False := by
  have hreal := div_le_div_of_nonneg_left hR hx hxr
  rw [hR₀,hR₁] at hreal
  have hsqx : x^2 ≤ r^2 := by nlinarith only [hx,hxr]
  have hsqy : v^2 ≤ y^2 := by nlinarith only [hv,hvy]
  have hdiff : 0 ≤ (r^2-3*v^2)-(x^2-3*y^2) := by linarith only [hsqx,hsqy]
  have hmul := mul_nonneg (show 0 ≤ α by linarith only [hα]) hdiff
  have hprod := mul_le_mul (show (1/2 : ℝ) ≤ α-1/10 by linarith only [hα]) hWedge
    (by norm_num : (0 : ℝ) ≤ 5/2) (show 0 ≤ α-1/10 by linarith only [hα])
  nlinarith only [hreal,hmul,hprod,hb,hA₀,hA₁]

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

theorem cube_quintic_pole_bounds (U D : ℝ) (hU : 5/2 ≤ U)
    (hD : (U - 8/15) ^ 2 ≤ D) :
    0 < D ∧ 0 ≤ (36/875) * (U-8/15) / D ∧
      (36/875) * (U-8/15) / D ≤ 1/40 ∧
      0 ≤ (36/875) * (2*U-8/15) / D ∧
      (36/875) * (2*U-8/15) / D ≤ 1/12 := by
  have hV : 0 < U - 8/15 := by linarith
  have hDp : 0 < D := lt_of_lt_of_le (sq_pos_of_pos hV) hD
  refine ⟨hDp,?_,?_,?_,?_⟩
  · exact div_nonneg (mul_nonneg (by norm_num) hV.le) hDp.le
  · apply (div_le_iff₀ hDp).2
    have hprod := mul_nonneg hV.le (show 0 ≤ U-8/15-40*(36/875) by linarith)
    nlinarith only [hD,hprod]
  · exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) hDp.le
  · apply (div_le_iff₀ hDp).2
    have hprod := mul_nonneg (show 0 ≤ U-8/15-3/2 by linarith)
      (show 0 ≤ U-8/15+3/10 by linarith)
    nlinarith only [hD,hprod,hU]

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

theorem cube_quintic_inverse_estimates (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < z.re) (hX : 5/2 ≤ z.re^2)
    (hβ : β/z = (1/10 : ℂ)*z^2-7/25+(36/875 : ℂ)/(z^2-8/15)) :
    let U := z.re^2+z.im^2
    let D := ‖z^2-(8/15 : ℂ)‖^2
    let A := (36/875)* (U-8/15)/D
    let B := -(36/875)* (U+8/15)/D
    β.re = z.re*((1/10)*(z.re^2-3*z.im^2)-7/25+A) ∧
      β.im = z.im*((1/10)*(3*z.re^2-z.im^2)-7/25+B) ∧
      0 ≤ A ∧ A ≤ 1/40 ∧ 0 ≤ (3*A-B)/2 ∧ (3*A-B)/2 ≤ 1/12 ∧
      5/2 ≤ z.re^2-3*z.im^2 ∧ 0 ≤ z.im ∧ (β.im = 0 → z.im = 0) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  have hpole : z^2-(8/15 : ℂ) ≠ 0 := by
    intro h
    have hn := congrArg norm (sub_eq_zero.mp h)
    norm_num [norm_pow,norm_div] at hn
    nlinarith only [hn,hX,Complex.sq_norm_sub_sq_re z,sq_nonneg z.im]
  obtain ⟨hRe,hIm,hphase,hD⟩ := rational_inverse_parts β z (1/10) (7/25) (36/875) (8/15)
    hz (by push_cast; exact hpole) (by push_cast; exact hβ)
  push_cast at hRe hIm hphase hD
  let U := z.re^2+z.im^2
  let D := ‖z^2-(8/15 : ℂ)‖^2
  let A := (36/875)* (U-8/15)/D
  let B := -(36/875)* (U+8/15)/D
  have hU : 5/2 ≤ U := by dsimp only [U]; nlinarith only [hX,sq_nonneg z.im]
  have hDlow : (U-8/15)^2 ≤ D := by dsimp only [U,D]; nlinarith only [hD,sq_nonneg z.im]
  obtain ⟨hDp,hA0,hA1,hC0,hC1⟩ := cube_quintic_pole_bounds U D hU hDlow
  have hCeq : (3*A-B)/2 = (36/875)*(2*U-8/15)/D := by dsimp only [A,B]; ring
  have hbr : 0 ≤ (1/10)*(z.re^2-3*z.im^2)-7/25+A := by
    apply nonneg_of_mul_nonneg_right ?_ hx
    simpa only [A,U,D] using (hRe ▸ hR)
  have hWedge : 5/2 ≤ z.re^2-3*z.im^2 := by linarith only [hbr,hA1]
  have hD1 : 1 ≤ D := by nlinarith only [hDlow,hU]
  have hk : 0 < (1/10 : ℝ)-(36/875)/D := by
    have hquot : (36/875 : ℝ)/D ≤ 36/875 := (div_le_iff₀ hDp).mpr (by linarith)
    linarith
  obtain ⟨hzim,hzero⟩ := quadrant_phase_forces_nonnegative_im β z _ hR hI hx hk hphase
  change _ ∧ _ ∧ 0 ≤ A ∧ A ≤ 1/40 ∧ 0 ≤ (3*A-B)/2 ∧ (3*A-B)/2 ≤ 1/12 ∧ _
  refine ⟨hRe,?_,hA0,hA1,?_,?_,hWedge,hzim,hzero⟩
  · simpa only [B,U,D,neg_mul,neg_div,sub_eq_add_neg] using hIm
  · rw [hCeq]; exact hC0
  · rw [hCeq]; exact hC1

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
theorem solution (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hwpos : 0 < w.re) (hwX : 5/2 ≤ w.re^2)
    (hwroot : w^5-10/3*w^3-10*β*w^2+40/21*w+16/3*β = 0)
    (hwinv : β/w = (1/10 : ℂ)*w^2-7/25+(36/875 : ℂ)/(w^2-8/15)) :
    ∃ z : ℂ, z^6-5*z^4-20*β*z^3+40/7*z^2+32*β*z-16/21+28*β^2 = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 5/2 ≤ z.re^2 ∧ 0 ≤ z.im ∧
      ∃ (α b : ℝ) (e : ℂ), 1/28 < α ∧ 1/25 < b-1/7 ∧
        β/z = (α : ℂ)*z^2-(b : ℂ)+e/z ∧ (β.im = 0 → z.im = 0) ∧
        (z.im ≠ 0 → (3*(e.re/z.re)-e.im/z.im)/2 ≤ 1/25) := by
  let W := w.re^2+w.im^2
  let Dw := ‖w^2-(8/15 : ℂ)‖^2
  let Aw := (36/875)*(W-8/15)/Dw
  let Bw := -(36/875)*(W+8/15)/Dw
  obtain ⟨hwR,hwI,_,hAw,_,hCw,hWedge,_,hwzero⟩ :=
    cube_quintic_inverse_estimates β w hR hI hwpos hwX hwinv
  let p : Polynomial ℂ := X^6-5*X^4-20*C β*X^3+C (40/7)*X^2+32*C β*X-C (16/21)+28*(C β)^2
  have hpdeg : p.natDegree = 6 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w = 0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 6*hwroot
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hX : 5/2 ≤ z.re^2 := by nlinarith only [hwX,hxz,hwpos]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hx
  have hzroot : z^6-5*z^4-20*β*z^3+40/7*z^2+32*β*z-16/21+28*β^2 = 0 := by
    simpa only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] using hz
  obtain ⟨α,b,e,hα,hb,hgraph,hzim,hzero,hreal,hC,hcases⟩ :=
    cube_sextic_inverse_estimates β z hR hI hx hX hzroot
  obtain ⟨hzR,hzI,_⟩ := cubic_graph_coordinate_parts β z e α b hz0 hgraph
  let Az := e.re/z.re
  let Bz := e.im/z.im
  have himorder : w.im ≤ z.im := by
    by_contra hfail
    have hlt : z.im < w.im := lt_of_not_ge hfail
    by_cases hzIm : z.im = 0
    · have hwIm := hwzero (hreal hzIm)
      linarith
    · have hv : 0 < z.im := lt_of_le_of_ne hzim (Ne.symm hzIm)
      have hy : 0 < w.im := lt_trans hv hlt
      have hR₀ : β.re/w.re = (1/10)*(w.re^2-3*w.im^2)-7/25+Aw := by
        rw [hwR]; dsimp only [Aw,W,Dw]; field_simp <;> ring
      have hI₀ : β.im/w.im = (1/10)*(3*w.re^2-w.im^2)-7/25+Bw := by
        rw [hwI]; dsimp only [Bw,W,Dw]; field_simp <;> ring
      have hR₁ : β.re/z.re = α*(z.re^2-3*z.im^2)-b+Az := by
        rw [hzR]; dsimp only [Az]; field_simp <;> ring
      have hI₁ : β.im/z.im = α*(3*z.re^2-z.im^2)-b+Bz := by
        rw [hzI]; dsimp only [Bz]; field_simp <;> ring
      rcases hcases with ⟨hslow,hgap,hCnonneg⟩ | ⟨hfast,hbup,hAlower⟩
      · exact inverse_graph_southeast_impossible (1/10) α (7/25) b Aw Az Bw Bz (1/12)
          β.re β.im w.re w.im z.re z.im (by linarith only [hα]) hslow hwpos hv hxz hlt.le hR hI
          hCw (hCnonneg hzIm) hgap hR₀ hI₀ hR₁ hI₁
      · exact fast_inverse_southeast_impossible β.re w.re w.im z.re z.im α b Aw Az
          hR hwpos hv.le hxz hlt.le hWedge hfast hbup hAw (hAlower hzIm) hR₀ hR₁
  exact ⟨z,hzroot,hxz,himorder,hX,hzim,α,b,e,hα,hb,hgraph,hzero,hC⟩
