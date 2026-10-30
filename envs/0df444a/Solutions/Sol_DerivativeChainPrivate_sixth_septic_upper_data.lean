-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_septic_upper_data
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:03:16.802723+00:00
-- url     : https://prove2.me/submissions/9d9d8e56-0370-4a86-b2d4-16083eeda871

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_cubic_graph_coordinate_parts
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_remainder_bounds
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_upper_graphs
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


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




set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cubic_graph_positive_phase_general (β z e : ℂ) (α b M T : ℝ)
    (hx : 0 < z.re) (hy : 0 < z.im) (hX : T ≤ z.re^2) (hT : 0 < T)
    (hα : 0 < α) (hgap : M < α*T)
    (hA : e.re/z.re ≤ M) (hB : -M ≤ e.im/z.im)
    (hgraph : β/z = (α:ℂ)*z^2-(b:ℂ)+e/z) : 0 < (β/z).im := by
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hxy : 0 < 2*z.re*z.im := by positivity
  have hU : T ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0 < 2*(z.re^2+z.im^2) := by positivity
  have hm := mul_le_mul_of_nonneg_left hU hα.le
  have hcorr : -α < (e.im/z.im-e.re/z.re)/(2*(z.re^2+z.im^2)) := by
    apply (lt_div_iff₀ hUp).mpr
    nlinarith only [hm,hgap,hA,hB]
  have hi := (cubic_graph_coordinate_parts β z e α b hz hgraph).2.2
  have hdiv : (β/z).im/(2*z.re*z.im) = α+(e/z).im/(2*z.re*z.im) := by
    rw [hi]; field_simp
  rw [quotient_imaginary_identity z e hx.ne' hy.ne'] at hdiv
  have hp : 0 < (β/z).im/(2*z.re*z.im) := by linarith
  exact (div_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2]) |>.1
end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sixth_septic_scalar_gaps :
    (3/100:ℝ)<(455-3*Real.sqrt 15145)/2720 ∧
    (455-3*Real.sqrt 15145)/2720<4/125 ∧
    (1/20:ℝ)<(455-3*Real.sqrt 19565)/680 ∧
    (455-3*Real.sqrt 19565)/680<3/50 ∧
    (455-3*Real.sqrt 15145)/2720<(455-3*Real.sqrt 19565)/680 ∧
    (1/20:ℝ)<(559-3*Real.sqrt 19565)/688-(13/32-77*Real.sqrt 15145/37280) ∧
    (29/1600:ℝ)<(559-3*Real.sqrt 19565)/688-(7/2)*((455-3*Real.sqrt 19565)/680) ∧
    (1/40:ℝ)<(13/32-77*Real.sqrt 15145/37280)-4*((455-3*Real.sqrt 15145)/2720) ∧
    (3/10:ℝ)<(455+3*Real.sqrt 15145)/2720 ∧
    13/32+77*Real.sqrt 15145/37280<2/3 ∧
    (1/5:ℝ)<(559-3*Real.sqrt 19565)/688 := by
  have h1:=Real.sq_sqrt (by norm_num : (0:ℝ)≤15145)
  have p1:=Real.sqrt_nonneg 15145
  have h2:=Real.sq_sqrt (by norm_num : (0:ℝ)≤19565)
  have p2:=Real.sqrt_nonneg 19565
  have l1 : (1230650:ℝ)/10000<Real.sqrt 15145 := by nlinarith only [h1,p1]
  have u1 : Real.sqrt 15145<(1230651:ℝ)/10000 := by nlinarith only [h1,p1]
  have l2 : (1398749:ℝ)/10000<Real.sqrt 19565 := by nlinarith only [h2,p2]
  have u2 : Real.sqrt 19565<(1398750:ℝ)/10000 := by nlinarith only [h2,p2]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [l1,u1,l2,u2]
end DerivativeChainPrivate

theorem solution (β z : ℂ) (hx : 0<z.re) (hy : 0<z.im) (hX : 7/2≤z.re^2)
    (hroot : (1360/13)*β^2*z-35*β*z^4+85*β*z^2-(1445/78)*β+
      z^7-7*z^5+(595/48)*z^3-(1445/312)*z=0) :
    ∃ α b : ℝ,∃ e : ℂ, 3/100<α ∧ β/z=(α:ℂ)*z^2-(b:ℂ)+e/z ∧ 0<(β/z).im ∧
      ((α=(455-3*Real.sqrt 15145)/2720 ∧ b=13/32-77*Real.sqrt 15145/37280 ∧
          e=sixthSepticRemainder z ∧ 0≤(3*(e.re/z.re)-e.im/z.im)/2) ∨
       (α=(455+3*Real.sqrt 15145)/2720 ∧ b=13/32+77*Real.sqrt 15145/37280 ∧
          0≤e.re/z.re ∧ e.re/z.re≤1/18 ∧ -(1/18)≤e.im/z.im ∧ e.im/z.im≤0)) := by
  obtain ⟨hAp,hAr,hBr,hBn⟩:=sixth_septic_remainder_bounds z hx hy hX
  obtain ⟨hαm,_,_,_,_,_,_,_,hαp,_,_⟩:=sixth_septic_scalar_gaps
  have hU : 7/2≤z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0<z.re^2+z.im^2 := by linarith
  have hsmall : (87/1000:ℝ)/(z.re^2+z.im^2)≤1/40 := by
    apply (div_le_iff₀ hUp).mpr
    linarith
  have hAu : (sixthSepticRemainder z).re/z.re≤1/40 := hAr.trans hsmall
  have hBl : -(1/40)≤(sixthSepticRemainder z).im/z.im := by
    rw [neg_div] at hBr
    linarith only [hBr,hsmall]
  have hCp : 0<(3*((sixthSepticRemainder z).re/z.re)-(sixthSepticRemainder z).im/z.im)/2 := by linarith
  rcases sixth_septic_upper_graphs β z hx hX hroot with hm|hp
  · refine ⟨(455-3*Real.sqrt 15145)/2720,13/32-77*Real.sqrt 15145/37280,
      sixthSepticRemainder z,hαm,hm,?_,Or.inl ⟨rfl,rfl,rfl,hCp.le⟩⟩
    exact cubic_graph_positive_phase_general β z (sixthSepticRemainder z) _ _ (1/40) (7/2)
      hx hy hX (by norm_num) (by linarith) (by linarith) hAu hBl hm
  · let E:=(17/96:ℂ)/z-sixthSepticRemainder z
    let U:=z.re^2+z.im^2
    have hU : 7/2≤U := by dsimp [U]; nlinarith [sq_nonneg z.im]
    have hUp : 0<U := by linarith
    have hUn : Complex.normSq z=U := by simp [U,Complex.normSq_apply,pow_two]
    have hArat : ((17/96:ℂ)/z).re/z.re=(17/96:ℝ)/U := by
      rw [div_eq_mul_inv]
      simp only [Complex.mul_re,Complex.div_re,Complex.inv_re,Complex.inv_im,hUn]
      norm_num
      field_simp
    have hBrat : ((17/96:ℂ)/z).im/z.im=-(17/96:ℝ)/U := by
      rw [div_eq_mul_inv]
      simp only [Complex.mul_im,Complex.div_im,Complex.inv_re,Complex.inv_im,hUn]
      norm_num
      field_simp
    have hAe : E.re/z.re=(17/96:ℝ)/U-(sixthSepticRemainder z).re/z.re := by
      simp only [E,Complex.sub_re,sub_div,hArat]
    have hBe : E.im/z.im=-(17/96:ℝ)/U-(sixthSepticRemainder z).im/z.im := by
      simp only [E,Complex.sub_im,sub_div,hBrat]
    have hcompare : (87/1000:ℝ)/U≤(17/96:ℝ)/U := div_le_div_of_nonneg_right (by norm_num) hUp.le
    have hbound : (17/96:ℝ)/U≤1/18 := by apply (div_le_iff₀ hUp).mpr; linarith
    change (sixthSepticRemainder z).re/z.re≤(87/1000:ℝ)/U at hAr
    change -(87/1000:ℝ)/U≤(sixthSepticRemainder z).im/z.im at hBr
    simp only [neg_div] at hBr hBe
    have hA0 : 0≤E.re/z.re := by rw [hAe]; linarith
    have hA1 : E.re/z.re≤1/18 := by rw [hAe]; linarith
    have hB0 : -(1/18)≤E.im/z.im := by rw [hBe]; linarith
    have hB1 : E.im/z.im≤0 := by rw [hBe]; linarith
    refine ⟨(455+3*Real.sqrt 15145)/2720,13/32+77*Real.sqrt 15145/37280,E,
      by linarith,hp,?_,Or.inr ⟨rfl,rfl,hA0,hA1,hB0,hB1⟩⟩
    exact cubic_graph_positive_phase_general β z E _ _ (1/18) (7/2) hx hy hX
      (by norm_num) (by linarith) (by linarith) hA1 hB0 hp
