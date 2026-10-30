-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_upper_data
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:07:06.758305+00:00
-- url     : https://prove2.me/submissions/e6ebea34-19f7-440b-9ab2-fdccd424a69e

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_cubic_graph_coordinate_parts
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_pole_corrections
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_remainder_bounds
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_upper_graphs
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

theorem sixth_octic_scalar_gaps :
    (1/50:ℝ)<(91-3*Real.sqrt 429)/1360 ∧ (91-3*Real.sqrt 429)/1360<11/500 ∧
    (91-3*Real.sqrt 429)/1360<(455-3*Real.sqrt 15145)/2720 ∧
    (3/100:ℝ)<(13/32-77*Real.sqrt 15145/37280)-(13/55-27*Real.sqrt 429/4840) ∧
    (11/100:ℝ)<(91+3*Real.sqrt 429)/1360 ∧
    13/55+27*Real.sqrt 429/4840<9/25 ∧
    (3/20:ℝ)<13/32-77*Real.sqrt 15145/37280 ∧
    (3/250:ℝ)<(13/55-27*Real.sqrt 429/4840)-(51/10)*((91-3*Real.sqrt 429)/1360) ∧
    (9/1000:ℝ)<(13/55-27*Real.sqrt 429/4840)-(26/5)*((91-3*Real.sqrt 429)/1360) ∧
    (455-3*Real.sqrt 15145)/2720<4/125 := by
  have h1:=Real.sq_sqrt (by norm_num : (0:ℝ)≤429)
  have p1:=Real.sqrt_nonneg 429
  have h2:=Real.sq_sqrt (by norm_num : (0:ℝ)≤15145)
  have p2:=Real.sqrt_nonneg 15145
  have l1 : (2071231517:ℝ)/100000000<Real.sqrt 429 := by nlinarith only [h1,p1]
  have u1 : Real.sqrt 429<(2071231518:ℝ)/100000000 := by nlinarith only [h1,p1]
  have l2 : (1230650:ℝ)/10000<Real.sqrt 15145 := by nlinarith only [h2,p2]
  have u2 : Real.sqrt 15145<(1230651:ℝ)/10000 := by nlinarith only [h2,p2]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [l1,u1,l2,u2]
end DerivativeChainPrivate

theorem solution (β z : ℂ) (hx : 0<z.re) (hy : 0<z.im) (hX : 4≤z.re^2)
    (hroot : (5440/13)*β^2*z^2-(92480/429)*β^2-56*β*z^5+(680/3)*β*z^3-(5780/39)*β*z+
      z^8-(28/3)*z^6+(595/24)*z^4-(1445/78)*z^2+24565/13728=0) :
    ∃ α b : ℝ,∃ e : ℂ, 1/50<α ∧ β/z=(α:ℂ)*z^2-(b:ℂ)+e/z ∧ 0<(β/z).im ∧
      ((α=(91-3*Real.sqrt 429)/1360 ∧ b=13/55-27*Real.sqrt 429/4840 ∧
          e=sixthOcticRemainder z ∧ 0≤(3*(e.re/z.re)-e.im/z.im)/2) ∨
       (α=(91+3*Real.sqrt 429)/1360 ∧ b=13/55+27*Real.sqrt 429/4840 ∧
          0≤e.re/z.re ∧ e.re/z.re≤1/20 ∧ -(1/20)≤e.im/z.im ∧ e.im/z.im≤0)) := by
  obtain ⟨hAp,hAr,hBr,hBn⟩:=sixth_octic_remainder_bounds z hx hy hX
  obtain ⟨hαm,_,_,_,hαp,_,_,_,_,_⟩:=sixth_octic_scalar_gaps
  have hU : 4≤z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0<z.re^2+z.im^2 := by linarith
  have hsmall : (7/100:ℝ)/(z.re^2+z.im^2)≤1/50 := by apply (div_le_iff₀ hUp).mpr; linarith
  have hAu : (sixthOcticRemainder z).re/z.re≤1/50 := hAr.trans hsmall
  have hBl : -(1/50)≤(sixthOcticRemainder z).im/z.im := by rw [neg_div] at hBr; linarith only [hBr,hsmall]
  have hCp : 0<(3*((sixthOcticRemainder z).re/z.re)-(sixthOcticRemainder z).im/z.im)/2 := by linarith
  rcases sixth_octic_upper_graphs β z hx hX hroot with hm|hp
  · refine ⟨(91-3*Real.sqrt 429)/1360,13/55-27*Real.sqrt 429/4840,sixthOcticRemainder z,
      hαm,hm,?_,Or.inl ⟨rfl,rfl,rfl,hCp.le⟩⟩
    exact cubic_graph_positive_phase_general β z (sixthOcticRemainder z) _ _ (1/50) 4
      hx hy hX (by norm_num) (by linarith) (by linarith) hAu hBl hm
  · let U:=z.re^2+z.im^2
    let P:=(1071/9680:ℂ)*z/(z^2-17/33)
    let E:=P-sixthOcticRemainder z
    obtain ⟨hPAlo,hPAhi,hPBlo,hPBhi⟩:=sixth_octic_pole_corrections z hx hy hX
    change (3/40:ℝ)/U≤P.re/z.re at hPAlo
    change P.re/z.re≤(13/100:ℝ)/U at hPAhi
    change -(17/100:ℝ)/U≤P.im/z.im at hPBlo
    change P.im/z.im≤-(9/100:ℝ)/U at hPBhi
    change (sixthOcticRemainder z).re/z.re≤(7/100:ℝ)/U at hAr
    change -(7/100:ℝ)/U≤(sixthOcticRemainder z).im/z.im at hBr
    simp only [neg_div] at hPBlo hPBhi hBr
    have hCompA : (7/100:ℝ)/U≤(3/40:ℝ)/U := div_le_div_of_nonneg_right (by norm_num) hUp.le
    have hCompB : (7/100:ℝ)/U≤(9/100:ℝ)/U := div_le_div_of_nonneg_right (by norm_num) hUp.le
    have hPAup : (13/100:ℝ)/U≤1/20 := by apply (div_le_iff₀ hUp).mpr; linarith
    have hPBup : (17/100:ℝ)/U≤1/20 := by apply (div_le_iff₀ hUp).mpr; linarith
    have hAe : E.re/z.re=P.re/z.re-(sixthOcticRemainder z).re/z.re := by simp only [E,Complex.sub_re,sub_div]
    have hBe : E.im/z.im=P.im/z.im-(sixthOcticRemainder z).im/z.im := by simp only [E,Complex.sub_im,sub_div]
    have hA0 : 0≤E.re/z.re := by rw [hAe]; linarith
    have hA1 : E.re/z.re≤1/20 := by rw [hAe]; linarith
    have hB0 : -(1/20)≤E.im/z.im := by rw [hBe]; linarith
    have hB1 : E.im/z.im≤0 := by rw [hBe]; linarith
    refine ⟨(91+3*Real.sqrt 429)/1360,13/55+27*Real.sqrt 429/4840,E,
      by linarith,hp,?_,Or.inr ⟨rfl,rfl,hA0,hA1,hB0,hB1⟩⟩
    exact cubic_graph_positive_phase_general β z E _ _ (1/20) 4 hx hy hX
      (by norm_num) (by linarith) (by linarith) hA1 hB0 hp
