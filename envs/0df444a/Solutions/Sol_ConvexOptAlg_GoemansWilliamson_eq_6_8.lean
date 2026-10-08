-- Prove2me | solution 1 for ConvexOptAlg.GoemansWilliamson.eq_6_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:44:16.715271+00:00
-- url     : https://prove2.me/submissions/5dce1052-3c67-4a92-be8c-a4144c04f9c1

import Mathlib
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs



namespace ConvexOptAlg.GoemansWilliamson

open Real

lemma gw_poly_neg (h : ℝ) (h1 : -1 ≤ h) (h2 : h ≤ 0) :
    0.311 * 3.141592 + h - 0.439 * 2.2214418 *
      (1 + h - h^2/2 - h^3/6 + 5/96 * h^4 - h^5/100) ≥ 0 := by
  nlinarith [sq_nonneg (h + 0.0257), mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 h2)) (sq_nonneg (h + 0.0257)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 h2)) (sq_nonneg h),
    mul_nonneg (neg_nonneg.2 h2) (sq_nonneg (h + 0.0257)),
    mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (h + 0.0257)), pow_two_nonneg (h^2)]

lemma gw_poly_neg' (h : ℝ) (h1 : -1 ≤ h) (h2 : h ≤ 0) :
    0.311 * 3.141592 + h - 0.439 * 2.2214406 *
      (1 + h - h^2/2 - h^3/6 + 5/96 * h^4 - h^5/100) ≥ 0 := by
  nlinarith [sq_nonneg (h + 0.0257), mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 h2)) (sq_nonneg (h + 0.0257)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 h2)) (sq_nonneg h),
    mul_nonneg (neg_nonneg.2 h2) (sq_nonneg (h + 0.0257)),
    mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (h + 0.0257)), pow_two_nonneg (h^2)]

lemma gw_poly_pos (h : ℝ) (h1 : 0 ≤ h) (h2 : h ≤ 0.8) :
    0.311 * 3.141592 + h - 0.439 * 2.2214418 *
      (1 + h - h^2/2 - h^3/6 + 5/96 * h^4 + h^5/100) ≥ 0 := by
  nlinarith [mul_nonneg h1 (sub_nonneg.2 h2), sq_nonneg h,
    mul_nonneg (mul_nonneg h1 (sub_nonneg.2 h2)) (sq_nonneg h),
    mul_nonneg (mul_nonneg h1 h1) (mul_nonneg h1 (sub_nonneg.2 h2)), pow_two_nonneg (h^2)]


lemma gw_theta (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ π) : 0.439 * π * (1 - cos θ) ≤ θ := by
  have pl := Real.pi_gt_d6
  have pu := Real.pi_lt_d6
  by_cases hc : θ ≤ 3 * π / 4 - 1
  · have h1 := Real.one_sub_sq_div_two_le_cos (x := θ)
    have hp0 : (0:ℝ) ≤ 0.439 * π := by positivity
    have hA : 0.439 * π * θ ≤ 0.439 * π * (3 * π / 4 - 1) := mul_le_mul_of_nonneg_left hc hp0
    have hB : π * π ≤ 3.141593 * 3.141593 := by nlinarith
    have : 0.439 * π * θ ≤ 2 := by nlinarith
    have hC : 0.439 * π * (1 - cos θ) ≤ 0.439 * π * (θ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hp0
    have hD : 0.439 * π * θ * θ ≤ 2 * θ := mul_le_mul_of_nonneg_right this h0
    nlinarith
  · push_neg at hc
    set h := θ - 3 * π / 4 with hh
    have hθ : θ = (π - π / 4) + h := by rw [hh]; ring
    have hcos : cos θ = -(√2 / 2) * (cos h + sin h) := by
      rw [hθ, Real.cos_add, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_four,
        Real.sin_pi_div_four]; ring
    have hh1 : -1 ≤ h := by linarith
    have hh2 : h ≤ 0.8 := by linarith
    have habs : |h| ≤ 1 := abs_le.2 ⟨hh1, by linarith⟩
    have cb := Real.cos_bound habs
    have sb := Real.sin_bound habs
    have cb' : cos h ≤ 1 - h^2/2 + |h|^4 * (5/96) := by linarith [(abs_le.1 cb).2]
    have sb' : sin h ≤ h - h^3/6 + |h|^5/100 := by linarith [(abs_le.1 sb).2]
    have s2 : (0:ℝ) ≤ √2 := Real.sqrt_nonneg _
    have s2sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have s2l : 1.41421356 ≤ √2 := by nlinarith
    have s2u : √2 ≤ 1.41421357 := by nlinarith
    have ql : 2.2214406 ≤ π * (√2 / 2) := by
      nlinarith [mul_le_mul pl.le s2l (by norm_num) (by positivity)]
    have qu : π * (√2 / 2) ≤ 2.2214418 := by
      nlinarith [mul_le_mul pu.le s2u s2 (by positivity)]
    -- u bound
    rcases le_total h 0 with hn | hp
    · have ha : |h| = -h := abs_of_nonpos hn
      rw [ha] at cb' sb'
      set u := 1 + h - h^2/2 - h^3/6 + 5/96 * h^4 - h^5/100 with hu
      have hcs : cos h + sin h ≤ u := by rw [hu]; linarith
      have key : 0.439 * π * (1 - cos θ) ≤ 0.439 * π + 0.439 * (π * (√2 / 2)) * u := by
        rw [hcos]
        have : 0 ≤ π * (√2 / 2) := by positivity
        linarith [mul_le_mul_of_nonneg_left hcs this]
      have e1 := gw_poly_neg h hh1 hn
      have e2 := gw_poly_neg' h hh1 hn
      rw [← hu] at e1 e2
      rcases le_total 0 u with hu0 | hu0
      · linarith [mul_le_mul_of_nonneg_right qu hu0]
      · linarith [mul_le_mul_of_nonpos_right ql hu0]
    · have ha : |h| = h := abs_of_nonneg hp
      rw [ha] at cb' sb'
      set u := 1 + h - h^2/2 - h^3/6 + 5/96 * h^4 + h^5/100 with hu
      have hcs : cos h + sin h ≤ u := by rw [hu]; linarith
      have key : 0.439 * π * (1 - cos θ) ≤ 0.439 * π + 0.439 * (π * (√2 / 2)) * u := by
        rw [hcos]
        have : 0 ≤ π * (√2 / 2) := by positivity
        linarith [mul_le_mul_of_nonneg_left hcs this]
      have e1 := gw_poly_pos h hp hh2
      rw [← hu] at e1
      have hu0 : 0 ≤ u := by
        rw [hu]; clear_value h; nlinarith [pow_nonneg hp 3, pow_nonneg hp 4, pow_nonneg hp 5, mul_nonneg hp hp]
      linarith [mul_le_mul_of_nonneg_right qu hu0]

theorem eq_6_8_core (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    1 - 2 / Real.pi * Real.arcsin t ≥ (0.878 : ℝ) * (1 - t) := by
  have hpi := Real.pi_pos
  have h1 := gw_theta (arccos t) (arccos_nonneg t) (arccos_le_pi t)
  rw [cos_arccos ht.1 ht.2] at h1
  rw [arcsin_eq_pi_div_two_sub_arccos]
  have : 1 - 2 / π * (π / 2 - arccos t) = 2 * arccos t / π := by field_simp; ring
  rw [this, ge_iff_le, le_div_iff₀ hpi]
  nlinarith

end ConvexOptAlg.GoemansWilliamson

open ConvexOptAlg.GoemansWilliamson


theorem solution (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    1 - 2 / Real.pi * Real.arcsin t ≥ (0.878 : ℝ) * (1 - t) := by
  exact eq_6_8_core t ht
