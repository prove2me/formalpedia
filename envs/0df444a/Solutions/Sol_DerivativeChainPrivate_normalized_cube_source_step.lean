-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_cube_source_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:16:58.608008+00:00
-- url     : https://prove2.me/submissions/7953d481-5b4d-4547-b52d-d81f4e9b1949

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_cubic_graph_coordinate_parts
import Theorems.Thm_DerivativeChainPrivate_derivative_real_supporting_parent
import Theorems.Thm_DerivativeChainPrivate_normalized_cube_actual_row_values
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



theorem iterated_derivative_real_parent (p : Polynomial ℂ) (k : ℕ)
    (hk : k < p.natDegree) (w : ℂ)
    (hw : (Polynomial.derivative^[k] p).eval w = 0) :
    ∃ z : ℂ, p.eval z = 0 ∧ w.re ≤ z.re := by
  induction k generalizing p w with
  | zero => exact ⟨w, hw, le_rfl⟩
  | succ k ih =>
    have hkd : k < p.derivative.natDegree := by rw [Polynomial.natDegree_derivative]; omega
    rw [Function.iterate_succ_apply] at hw
    obtain ⟨u, hu, hwu⟩ := ih p.derivative hkd w hw
    obtain ⟨z, hz, huz⟩ := derivative_real_supporting_parent p (by omega) u hu
    exact ⟨z, hz, hwu.trans huz⟩

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
theorem solution (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im)
    (hwroot : w^6-5*w^4-20*β*w^3+40/7*w^2+32*β*w-16/21+28*β^2 = 0)
    (α b : ℝ) (e : ℂ) (hα : 1/28 < α) (hb : 1/25 < b-1/7)
    (hgraph : β/w = (α : ℂ)*w^2-(b : ℂ)+e/w)
    (hwzero : β.im = 0 → w.im = 0)
    (hC : w.im ≠ 0 → (3*(e.re/w.re)-e.im/w.im)/2 ≤ 1/25) :
    ∃ z : ℂ, z^3-4*z-28*β = 0 ∧ w.re ≤ z.re ∧ w.im ≤ z.im ∧ 0 < z.re := by
  let q : Polynomial ℂ := X^3-4*X-28*C β
  let p := q^3
  have hpdeg : p.natDegree = 9 := by dsimp only [p,q]; compute_degree <;> norm_num
  have hactual : (derivative^[3] p).eval w = 0 := by
    have h := (normalized_cube_actual_row_values β w).1
    rw [hwroot,mul_zero] at h
    exact h
  obtain ⟨z,hz,hxz⟩ := iterated_derivative_real_parent p 3 (by rw [hpdeg]; norm_num) w hactual
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hz0 : z ≠ 0 := by intro h; simp [h] at hx
  have hw0 : w ≠ 0 := by intro h; simp [h] at hwpos
  have hzq : q.eval z = 0 := by
    have hpow : (q.eval z)^3 = 0 := by simpa only [p,eval_pow] using hz
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hpow
  have hzroot : z^3-4*z-28*β = 0 := by
    simpa only [q,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat] using hzq
  have hzinv : β/z = (1/28 : ℂ)*z^2-1/7+0/(z^2-0) := by
    simp only [zero_div,add_zero]
    apply (div_eq_iff hz0).2
    linear_combination (-1/28 : ℂ)*hzroot
  obtain ⟨hzR,hzI,hzphase,_⟩ := rational_inverse_parts β z (1/28) (1/7) 0 0 hz0
    (by simpa using pow_ne_zero 2 hz0) (by push_cast; exact hzinv)
  simp only [Complex.ofReal_zero,sub_zero,zero_mul,mul_zero,zero_div,add_zero] at hzR hzI hzphase
  obtain ⟨hzim,_⟩ := quadrant_phase_forces_nonnegative_im β z (1/28) hR hI hx (by norm_num) hzphase
  obtain ⟨hwR,hwI,_⟩ := cubic_graph_coordinate_parts β w e α b hw0 hgraph
  have himorder : w.im ≤ z.im := by
    by_contra hfail
    have hlt : z.im < w.im := lt_of_not_ge hfail
    by_cases hzIm : z.im = 0
    · have hβzero : β.im = 0 := by rw [hzI,hzIm,zero_mul]
      have hwIm := hwzero hβzero
      linarith
    · have hv : 0 < z.im := lt_of_le_of_ne hzim (Ne.symm hzIm)
      have hy : 0 < w.im := lt_trans hv hlt
      apply inverse_graph_southeast_impossible α (1/28) b (1/7)
        (e.re/w.re) 0 (e.im/w.im) 0 (1/25)
        β.re β.im w.re w.im z.re z.im
        (by norm_num) hα hwpos hv hxz hlt.le hR hI (hC hy.ne') (by norm_num) hb
      · rw [hwR]; field_simp <;> ring
      · rw [hwI]; field_simp <;> ring
      · rw [hzR]; field_simp <;> ring
      · rw [hzI]; field_simp <;> ring
  exact ⟨z,hzroot,hxz,himorder,hx⟩
