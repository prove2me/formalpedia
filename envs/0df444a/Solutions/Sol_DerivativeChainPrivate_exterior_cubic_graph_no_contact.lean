-- Prove2me | solution 1 for DerivativeChainPrivate.exterior_cubic_graph_no_contact
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T11:12:35.541859+00:00
-- url     : https://prove2.me/submissions/28be969c-9995-499e-bc49-8ca511c150cb

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false
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



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem inverse_graph_vertical_impossible (α₀ α₁ b₀ b₁ A₀ A₁ M x y v : ℝ)
    (hα₁ : 0 < α₁) (hα : α₁ < α₀) (hy : 0 ≤ y) (hv : y ≤ v)
    (hA₀ : 0 ≤ A₀) (hA₁ : A₁ ≤ M)
    (hgap : M < b₁ - (α₁ / α₀) * b₀)
    (hsource : 0 ≤ α₀ * (x ^ 2 - 3 * y ^ 2) - b₀ + A₀)
    (heq : α₀ * (x ^ 2 - 3 * y ^ 2) - b₀ + A₀ =
      α₁ * (x ^ 2 - 3 * v ^ 2) - b₁ + A₁) : False := by
  have hα₀ : 0 < α₀ := lt_trans hα₁ hα
  have hg : M * α₀ < b₁ * α₀ - α₁ * b₀ := by
    have hm := (mul_lt_mul_iff_left₀ hα₀).mpr hgap
    have hid : (b₁ - α₁ / α₀ * b₀) * α₀ = b₁ * α₀ - α₁ * b₀ := by
      field_simp
    rw [hid] at hm
    nlinarith only [hm]
  have hs := mul_nonneg (sub_pos.mpr hα).le hsource
  have ha := mul_nonneg hα₁.le hA₀
  have hb := (mul_le_mul_iff_right₀ hα₀).mpr hA₁
  have hv2 : y ^ 2 ≤ v ^ 2 := by nlinarith only [hy,hv]
  have hc := mul_nonneg (mul_pos hα₀ hα₁).le (sub_nonneg.mpr hv2)
  have hid : (α₀ - α₁) * (α₀ * (x ^ 2 - 3 * y ^ 2) - b₀ + A₀) +
      (α₀ * b₁ - α₁ * b₀ + α₁ * A₀ - α₀ * A₁) +
      3 * (α₀ * α₁) * (v ^ 2 - y ^ 2) = 0 := by
    calc
      _ = α₀ * ((α₀ * (x ^ 2 - 3 * y ^ 2) - b₀ + A₀) -
          (α₁ * (x ^ 2 - 3 * v ^ 2) - b₁ + A₁)) := by ring
      _ = 0 := by rw [heq]; ring
  nlinarith only [hg, hs, ha, hb, hc, hid]

theorem inverse_graph_horizontal_impossible (α₀ α₁ b₀ b₁ A₀ A₁ C₀ C₁ K x y r : ℝ)
    (hα : α₁ < α₀) (hC₀ : C₀ ≤ K) (hC₁ : 0 ≤ C₁)
    (hgap : K < b₀ - b₁)
    (hre : α₁ * (r ^ 2 - 3 * y ^ 2) - b₁ + A₁ ≤
      α₀ * (x ^ 2 - 3 * y ^ 2) - b₀ + A₀)
    (him : α₀ * (3 * x ^ 2 - y ^ 2) - b₀ + 3 * A₀ - 2 * C₀ =
      α₁ * (3 * r ^ 2 - y ^ 2) - b₁ + 3 * A₁ - 2 * C₁) : False := by
  have hterm := mul_nonneg (sub_pos.mpr hα).le (sq_nonneg y)
  nlinarith only [hre, him, hterm, hC₀, hC₁, hgap]



end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution (w z e₀ e₁ : ℂ)
    (α₀ α₁ b₀ b₁ M K : ℝ)
    (hwre : 0 < w.re) (hwim : 0 < w.im)
    (hα₁ : 0 < α₁) (hα : α₁ < α₀)
    (hsource : 0 ≤ ((α₀ : ℂ) * w ^ 3 - (b₀ : ℂ) * w + e₀).re)
    (hA₀ : 0 ≤ e₀.re / w.re) (hA₁ : e₁.re / z.re ≤ M)
    (hC₀ : (3 * (e₀.re / w.re) - e₀.im / w.im) / 2 ≤ K)
    (hC₁ : 0 ≤ (3 * (e₁.re / z.re) - e₁.im / z.im) / 2)
    (hvertical : M < b₁ - (α₁ / α₀) * b₀)
    (hhorizontal : K < b₀ - b₁)
    (hboundary : (z.re = w.re ∧ w.im ≤ z.im) ∨ (w.re ≤ z.re ∧ z.im = w.im)) :
    (α₀ : ℂ) * w ^ 3 - (b₀ : ℂ) * w + e₀ ≠
      (α₁ : ℂ) * z ^ 3 - (b₁ : ℂ) * z + e₁ := by
  intro heq
  have hreal (t e : ℂ) (a b : ℝ) :
      ((a : ℂ) * t ^ 3 - (b : ℂ) * t + e).re =
        t.re * (a * (t.re ^ 2 - 3 * t.im ^ 2) - b) + e.re := by
    simp only [pow_succ, pow_zero, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im]
    ring
  have himag (t e : ℂ) (a b : ℝ) :
      ((a : ℂ) * t ^ 3 - (b : ℂ) * t + e).im =
        t.im * (a * (3 * t.re ^ 2 - t.im ^ 2) - b) + e.im := by
    simp only [pow_succ, pow_zero, Complex.add_im, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im]
    ring
  have hrealdiv (t e : ℂ) (a b : ℝ) (ht : 0 < t.re) :
      a * (t.re ^ 2 - 3 * t.im ^ 2) - b + e.re / t.re =
        ((a : ℂ) * t ^ 3 - (b : ℂ) * t + e).re / t.re := by
    rw [hreal]
    field_simp
  have himagdiv (t e : ℂ) (a b : ℝ) (ht : 0 < t.im) :
      a * (3 * t.re ^ 2 - t.im ^ 2) - b + 3 * (e.re / t.re) -
        2 * ((3 * (e.re / t.re) - e.im / t.im) / 2) =
        ((a : ℂ) * t ^ 3 - (b : ℂ) * t + e).im / t.im := by
    rw [himag]
    field_simp
    ring
  rcases hboundary with ⟨hzre, hzim⟩ | ⟨hzre, hzim⟩
  · apply inverse_graph_vertical_impossible α₀ α₁ b₀ b₁
      (e₀.re / w.re) (e₁.re / z.re) M w.re w.im z.im hα₁ hα hwim.le hzim hA₀ hA₁ hvertical
    · rw [hrealdiv w e₀ α₀ b₀ hwre]
      exact div_nonneg hsource hwre.le
    · conv_rhs => rw [← hzre]
      rw [hrealdiv w e₀ α₀ b₀ hwre, hrealdiv z e₁ α₁ b₁ (by simpa [hzre] using hwre),
        heq, hzre]
  · have hzpos : 0 < z.re := lt_of_lt_of_le hwre hzre
    apply inverse_graph_horizontal_impossible α₀ α₁ b₀ b₁
      (e₀.re / w.re) (e₁.re / z.re)
      ((3 * (e₀.re / w.re) - e₀.im / w.im) / 2)
      ((3 * (e₁.re / z.re) - e₁.im / z.im) / 2) K w.re w.im z.re
      hα hC₀ hC₁ hhorizontal
    · conv_lhs => rw [← hzim]
      rw [hrealdiv z e₁ α₁ b₁ hzpos, hrealdiv w e₀ α₀ b₀ hwre, ← heq]
      exact div_le_div_of_nonneg_left hsource hwre hzre
    · conv_rhs => rw [← hzim]
      rw [himagdiv w e₀ α₀ b₀ hwim,
        himagdiv z e₁ α₁ b₁ (by simpa [hzim] using hwim), heq, hzim]
