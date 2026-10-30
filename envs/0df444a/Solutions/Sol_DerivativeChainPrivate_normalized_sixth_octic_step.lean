-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_sixth_octic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:13:26.873386+00:00
-- url     : https://prove2.me/submissions/3fefd35c-d5b5-4e0c-92a1-efa05a26b2f4

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_cubic_graph_coordinate_parts
import Theorems.Thm_DerivativeChainPrivate_derivative_real_supporting_parent
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_nonnegative_im
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_upper_data
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_selected_bounds
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_sharp_C_bound
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fast_graph_northeast_impossible
    (α₀ α₁ b₀ b₁ A₁ B₀ B₁ Xmin K R I x y r v : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxr : x ≤ r) (hyv : y ≤ v)
    (hR : 0 ≤ R) (hI : 0 ≤ I) (hX : Xmin ≤ x^2)
    (hα₀ : 0 ≤ α₀) (hα₁ : 0 ≤ α₁) (hα : 3*α₀ < 8*α₁/3)
    (hB₀ : B₀ ≤ 0) (hcorrection : -K ≤ B₁-A₁/3)
    (hgap : 2*b₁/3-b₀+K < (8*α₁/3-3*α₀)*Xmin)
    (hI₀ : I/y = α₀*(3*x^2-y^2)-b₀+B₀)
    (hR₁ : R/r = α₁*(r^2-3*v^2)-b₁+A₁)
    (hI₁ : I/v = α₁*(3*r^2-v^2)-b₁+B₁) : False := by
  have hr : 0 < r := lt_of_lt_of_le hx hxr
  have hv : 0 < v := lt_of_lt_of_le hy hyv
  have hcmp := div_le_div_of_nonneg_left hI hy hyv
  rw [hI₀,hI₁] at hcmp
  have hrr : x^2 ≤ r^2 := by nlinarith only [hx,hxr]
  have hmul := mul_le_mul_of_nonneg_left hrr hα₁
  have hyterm := mul_nonneg hα₀ (sq_nonneg y)
  have hreal : 0 ≤ α₁*(r^2-3*v^2)-b₁+A₁ := by rw [← hR₁]; positivity
  have hxmin := mul_le_mul_of_nonneg_left hX (show 0 ≤ 8*α₁/3-3*α₀ by linarith)
  nlinarith only [hcmp,hmul,hyterm,hreal,hxmin,hgap,hB₀,hcorrection]

end DerivativeChainPrivate

namespace DerivativeChainPrivate



end DerivativeChainPrivate

namespace DerivativeChainPrivate



end DerivativeChainPrivate

namespace DerivativeChainPrivate

theorem inverse_graph_large_slope_southeast_impossible
    (R x y r v α₀ α₁ b₀ b₁ A₀ A₁ W K₀ K₁ : ℝ)
    (hR : 0 ≤ R) (hx : 0 < x) (hv : 0 ≤ v) (hxr : x ≤ r) (hvy : v ≤ y)
    (hW : W ≤ x^2-3*y^2) (hα₁ : 0 ≤ α₁) (hα : α₀ < α₁)
    (hA₀ : A₀ ≤ K₀) (hA₁ : K₁ ≤ A₁)
    (hgap : b₁-b₀+K₀-K₁ < (α₁-α₀)*W)
    (hR₀ : R/x = α₀*(x^2-3*y^2)-b₀+A₀)
    (hR₁ : R/r = α₁*(r^2-3*v^2)-b₁+A₁) : False := by
  have hreal := div_le_div_of_nonneg_left hR hx hxr
  rw [hR₀,hR₁] at hreal
  have hsqx : x^2 ≤ r^2 := by nlinarith only [hx,hxr]
  have hsqy : v^2 ≤ y^2 := by nlinarith only [hv,hvy]
  have hdiff : 0 ≤ (r^2-3*v^2)-(x^2-3*y^2) := by linarith only [hsqx,hsqy]
  have hmul := mul_nonneg hα₁ hdiff
  have hprod := mul_le_mul_of_nonneg_left hW (sub_nonneg.mpr hα.le)
  nlinarith only [hreal,hmul,hprod,hgap,hA₀,hA₁]

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



theorem solution (β w : ℂ) (hR : 0≤β.re) (hI : 0<β.im)
    (hwpos : 0<w.re) (hwim : 0<w.im) (hwX : 4≤w.re^2)
    (hwroot : (1360/13)*β^2*w-35*β*w^4+85*β*w^2-(1445/78)*β+
      w^7-7*w^5+(595/48)*w^3-(1445/312)*w=0)
    (hwinv : β/w=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*w^2-
      ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder w/w) :
    ∃ z : ℂ,
      (5440/13)*β^2*z^2-(92480/429)*β^2-56*β*z^5+(680/3)*β*z^3-(5780/39)*β*z+
        z^8-(28/3)*z^6+(595/24)*z^4-(1445/78)*z^2+24565/13728=0 ∧
      w.re≤z.re ∧ w.im≤z.im ∧
      β/z=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-
        ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder z/z := by
  let α₀:=(455-3*Real.sqrt 15145)/2720
  let b₀:=13/32-77*Real.sqrt 15145/37280
  obtain ⟨hαm,_,hαm0,hgap,hαp,hbfast,hb₀lo,_,_,hα₀up⟩:=sixth_octic_scalar_gaps
  change α₀<4/125 at hα₀up
  change (3/20:ℝ)<b₀ at hb₀lo
  have hα₀ : 0<α₀ := by
    have hh:=sixth_septic_scalar_gaps.1
    change (3/100:ℝ)<α₀ at hh
    linarith
  obtain ⟨_,hA₀hi,hB₀hi,_,hWedge⟩:=sixth_septic_selected_bounds β w hR hwpos hwim (by linarith) hwinv
  have hC₀hi:=sixth_septic_sharp_C_bound w hwpos hwim hwX
  have hw : w≠0 := by intro he; simp [he] at hwpos
  obtain ⟨hr₀,hi₀,_⟩:=cubic_graph_coordinate_parts β w (sixthSepticRemainder w) α₀ b₀ hw hwinv
  have hR₀ : β.re/w.re=α₀*(w.re^2-3*w.im^2)-b₀+(sixthSepticRemainder w).re/w.re := by rw [hr₀]; field_simp
  have hI₀ : β.im/w.im=α₀*(3*w.re^2-w.im^2)-b₀+(sixthSepticRemainder w).im/w.im := by rw [hi₀]; field_simp
  let p : Polynomial ℂ := X^8-C (28/3)*X^6-C (56*β)*X^5+C (595/24)*X^4+
    C ((680/3)*β)*X^3+C ((5440/13)*β^2-1445/78)*X^2-C ((5780/39)*β)*X+
    C (24565/13728-(92480/429)*β^2)
  have hpdeg : p.natDegree=8 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w=0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 8*hwroot
  obtain ⟨z,hz,hxz⟩:=derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx : 0<z.re := lt_of_lt_of_le hwpos hxz
  have hX : 4≤z.re^2 := by nlinarith only [hwX,hwpos,hxz]
  have hz0 : z≠0 := by intro he; simp [he] at hx
  have hzroot : (5440/13)*β^2*z^2-(92480/429)*β^2-56*β*z^5+(680/3)*β*z^3-(5780/39)*β*z+
      z^8-(28/3)*z^6+(595/24)*z^4-(1445/78)*z^2+24565/13728=0 := by
    have he:=hz
    simp only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] at he
    linear_combination he
  obtain ⟨hy0,hzero⟩:=sixth_octic_nonnegative_im β z hR hI.le hx hX hzroot
  have hy : 0<z.im := by
    by_contra hn
    have he : z.im=0 := le_antisymm (le_of_not_gt hn) hy0
    have := hzero.mpr he
    linarith
  obtain ⟨α,b,e,hα,hgraph,_,hcases⟩:=sixth_octic_upper_data β z hx hy hX hzroot
  obtain ⟨hr₁,hi₁,_⟩:=cubic_graph_coordinate_parts β z e α b hz0 hgraph
  have hR₁ : β.re/z.re=α*(z.re^2-3*z.im^2)-b+e.re/z.re := by rw [hr₁]; field_simp
  have hI₁ : β.im/z.im=α*(3*z.re^2-z.im^2)-b+e.im/z.im := by rw [hi₁]; field_simp
  have hslow : α=(91-3*Real.sqrt 429)/1360 ∧ b=13/55-27*Real.sqrt 429/4840 ∧
      e=sixthOcticRemainder z ∧ 0≤(3*(e.re/z.re)-e.im/z.im)/2 := by
    rcases hcases with hs|⟨ha,hb,hAlo,hAhi,hBlo,hBhi⟩
    · exact hs
    · exfalso
      subst α
      subst b
      by_cases hvy : z.im≤w.im
      · exact inverse_graph_large_slope_southeast_impossible β.re w.re w.im z.re z.im α₀ _ b₀ _
          ((sixthSepticRemainder w).re/w.re) (e.re/z.re) 4 (39/2000) 0 hR hwpos hy.le hxz hvy hWedge
          (by linarith) (by linarith only [hαp,hα₀up]) hA₀hi hAlo
          (by linarith only [hαp,hα₀up,hb₀lo,hbfast]) hR₀ hR₁
      · exact fast_graph_northeast_impossible α₀ _ b₀ _ (e.re/z.re) ((sixthSepticRemainder w).im/w.im) (e.im/z.im)
          4 (1/15) β.re β.im w.re w.im z.re z.im hwpos hwim hxz (le_of_not_ge hvy)
          hR hI.le hwX hα₀.le (by linarith) (by linarith) hB₀hi (by linarith)
          (by linarith only [hαp,hα₀up,hb₀lo,hbfast]) hI₀ hR₁ hI₁
  rcases hslow with ⟨rfl,rfl,rfl,hC₁⟩
  have himorder : w.im≤z.im := by
    by_contra hn
    exact inverse_graph_southeast_impossible α₀ _ b₀ _ ((sixthSepticRemainder w).re/w.re) ((sixthOcticRemainder z).re/z.re)
      ((sixthSepticRemainder w).im/w.im) ((sixthOcticRemainder z).im/z.im) (3/100) β.re β.im w.re w.im z.re z.im
      (by linarith) hαm0 hwpos hy hxz (le_of_not_ge hn) hR hI.le hC₀hi hC₁ hgap hR₀ hI₀ hR₁ hI₁
  exact ⟨z,hzroot,hxz,himorder,hgraph⟩
