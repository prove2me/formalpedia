-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_sextic_selected_graph
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:09:04.885709+00:00
-- url     : https://prove2.me/submissions/1857b420-8523-4f74-897c-113c6e4f2bc7

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Theorems.Thm_DerivativeChainPrivate_cubic_graph_coordinate_parts
import Theorems.Thm_DerivativeChainPrivate_sixth_quintic_estimates
import Theorems.Thm_DerivativeChainPrivate_sixth_sextic_nonnegative_im
import Theorems.Thm_DerivativeChainPrivate_sixth_sextic_upper_data
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

theorem fast_graph_southeast_impossible (R x y r v α b b₀ A₀ A₁ : ℝ)
    (hR : 0 ≤ R) (hx : 0 < x) (hv : 0 ≤ v) (hxr : x ≤ r) (hvy : v ≤ y)
    (hWedge : 5/2 ≤ x^2-3*y^2) (hα : 9/10 < α) (hb : b < 3/2) (hb₀ : 1/4 ≤ b₀)
    (hA₀ : A₀ ≤ 3/100) (hA₁ : -(3/100) ≤ A₁)
    (hR₀ : R/x = (1/10)*(x^2-3*y^2)-b₀+A₀)
    (hR₁ : R/r = α*(r^2-3*v^2)-b+A₁) : False := by
  have hreal := div_le_div_of_nonneg_left hR hx hxr
  rw [hR₀,hR₁] at hreal
  have hsqx : x^2 ≤ r^2 := by nlinarith only [hx,hxr]
  have hsqy : v^2 ≤ y^2 := by nlinarith only [hv,hvy]
  have hdiff : 0 ≤ (r^2-3*v^2)-(x^2-3*y^2) := by linarith only [hsqx,hsqy]
  have hmul := mul_nonneg (show 0 ≤ α by linarith only [hα]) hdiff
  have hprod := mul_le_mul (show (4/5:ℝ) ≤ α-1/10 by linarith only [hα]) hWedge
    (by norm_num : (0:ℝ) ≤ 5/2) (show 0 ≤ α-1/10 by linarith only [hα])
  nlinarith only [hreal,hmul,hprod,hb,hb₀,hA₀,hA₁]

end DerivativeChainPrivate

namespace DerivativeChainPrivate



end DerivativeChainPrivate

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (β w z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im) (hwX : 5/2 ≤ w.re^2)
    (hwinv : β/w = (1/10:ℂ)*w^2-41/140+(459/7840:ℂ)/(w^2-17/42))
    (hxz : w.re ≤ z.re) (hzI : 0 < z.im)
    (hzroot : (1360/91)*β^2-20*β*z^3+(170/7)*β*z+z^6-5*z^4+(85/16)*z^2-1445/2184=0) :
    β/z = (((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*z^2-(((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+
      ((3*Real.sqrt 19565/680:ℝ):ℂ)*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) := by
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hX : 5/2 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hxz]
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hw : w ≠ 0 := by intro he; simp [he] at hwpos
  have hy : 0 < w.im := by
    by_contra hn
    have hw0 : w.im=0 := le_antisymm (le_of_not_gt hn) hwim
    have hwreal : w = (w.re:ℂ) := by apply Complex.ext <;> simp [hw0]
    have heq := (div_eq_iff hw).mp hwinv
    rw [hwreal] at heq
    have hi := congrArg Complex.im heq
    norm_num [Complex.mul_im,Complex.mul_re,Complex.div_im,pow_two] at hi
    have hzero := (sixth_sextic_nonnegative_im μ hsupp hμ β z hR hI hx hX hzroot).2.mp hi
    linarith
  obtain ⟨hAw0,hAw,hBw,hCw,hWedge,hR₀,hI₀,_⟩ :=
    sixth_quintic_estimates β w hR hI hwpos hwim hwX hwinv
  let A₀ := (459/7840:ℝ)*(w.re^2+w.im^2-17/42)/‖w^2-(17/42:ℂ)‖^2
  let B₀ := -(459/7840:ℝ)*(w.re^2+w.im^2+17/42)/‖w^2-(17/42:ℂ)‖^2
  obtain ⟨α,b,e,hα,hgraph,_,hcases⟩ := sixth_sextic_upper_data μ hsupp hμ β z hx hzI hX hzroot
  rcases hcases with ⟨ha,hb,he,_,_,_⟩ | ⟨hfast,hbup,hAlower,hAup,hBlo⟩
  · rw [ha,hb,he] at hgraph
    convert hgraph using 1
    field_simp
  · exfalso
    obtain ⟨hr,hi,_⟩ := cubic_graph_coordinate_parts β z e α b hz hgraph
    have hR₁ : β.re/z.re = α*(z.re^2-3*z.im^2)-b+e.re/z.re := by rw [hr]; field_simp
    have hI₁ : β.im/z.im = α*(3*z.re^2-z.im^2)-b+e.im/z.im := by rw [hi]; field_simp
    by_cases hvy : z.im ≤ w.im
    · exact fast_graph_southeast_impossible β.re w.re w.im z.re z.im α b (41/140) A₀ (e.re/z.re)
        hR hwpos hzI.le hxz hvy hWedge hfast (by linarith) (by norm_num)
        hAw (by linarith) hR₀ hR₁
    · exact fast_graph_northeast_impossible (1/10) α (41/140) b (e.re/z.re) B₀ (e.im/z.im)
        (5/2) 0 β.re β.im w.re w.im z.re z.im hwpos hy hxz (le_of_not_ge hvy) hR hI hwX
        (by norm_num) (by linarith) (by linarith) hBw (by linarith) (by linarith) (hI₀ hy) hR₁ hI₁
