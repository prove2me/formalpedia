-- Prove2me | solution 1 for DynOpaque.TwoPeriod.lemma_2_corners_dominated
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T01:56:37.583857+00:00
-- url     : https://prove2.me/submissions/4f7046b3-e8d9-4edf-b375-479ae8d31114

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaqueCornersAux

/-- Objective (3) in the normalized variables `c = cH - cL`, `d = vHL - cL`. -/
noncomputable def f (α c d x y : ℝ) : ℝ := x * (d - c * x) + (α * x + (1 - α) * y) * (d - c * y)

/-- Concave case: for `D = 4 - 4α - α² > 0`, `D c f ≤ 2(1-α) d²` everywhere. -/
theorem boundI (α c d x y : ℝ) (hD : 0 < 4 - 4 * α - α ^ 2) :
    (4 - 4 * α - α ^ 2) * c * f α c d x y ≤ 2 * (1 - α) * d ^ 2 := by
  have key : (4 - 4 * α - α ^ 2) * (2 * (1 - α) * d ^ 2 - (4 - 4 * α - α ^ 2) * c * f α c d x y) =
      ((4 - 4 * α - α ^ 2) * c * x - (2 - α - α ^ 2) * d +
          α * ((4 - 4 * α - α ^ 2) * c * y - (2 - 3 * α - α ^ 2) * d) / 2) ^ 2 +
        (4 - 4 * α - α ^ 2) * ((4 - 4 * α - α ^ 2) * c * y - (2 - 3 * α - α ^ 2) * d) ^ 2 / 4 := by
    unfold f; ring
  have hr : 0 ≤ (4 - 4 * α - α ^ 2) * (2 * (1 - α) * d ^ 2 - (4 - 4 * α - α ^ 2) * c * f α c d x y) := by
    rw [key]; positivity
  have := (mul_nonneg_iff_of_pos_left hD).1 hr
  linarith

/-- Case `α² + 3α ≥ 2`: on the nonnegative quadrant, `4 c f ≤ (1+α)² d²`. -/
theorem boundII (α c d x y : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (hk : 0 ≤ α ^ 2 + 3 * α - 2)
    (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    4 * c * f α c d x y ≤ (1 + α) ^ 2 * d ^ 2 := by
  have key : (1 + α) ^ 2 * ((1 + α) ^ 2 * d ^ 2 - 4 * c * f α c d x y) =
      ((1 + α) * ((1 + α) * d - 2 * c * x) - 2 * c * (1 - α) * y) ^ 2 +
        4 * c ^ 2 * (1 - α) * (α ^ 2 + 3 * α) * y ^ 2 +
        4 * c ^ 2 * (1 + α) * (α ^ 2 + 3 * α - 2) * x * y := by
    unfold f; ring
  have h1a : 0 ≤ 1 - α := by linarith
  have hr : 0 ≤ (1 + α) ^ 2 * ((1 + α) ^ 2 * d ^ 2 - 4 * c * f α c d x y) := by
    rw [key]
    have : 0 ≤ 4 * c ^ 2 * (1 - α) * (α ^ 2 + 3 * α) * y ^ 2 := by positivity
    have : 0 ≤ 4 * c ^ 2 * (1 + α) * (α ^ 2 + 3 * α - 2) * x * y := by positivity
    positivity
  have hp : 0 < (1 + α) ^ 2 := by positivity
  have := (mul_nonneg_iff_of_pos_left hp).1 hr
  linarith

/-- `f` is affine in `d`. -/
theorem f_affine (α c d d0 x y : ℝ) :
    f α c d x y = f α c d0 x y + (d - d0) * (x + (α * x + (1 - α) * y)) := by
  unfold f; ring

/-- Corner regime, concave case. -/
theorem cornerI (α c d x y : ℝ) (h0 : 0 ≤ α) (hk : α ^ 2 + 3 * α < 2) (hc : 0 < c)
    (hd : (4 - 4 * α - α ^ 2) * c ≤ (2 - α - α ^ 2) * d)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    f α c d x y ≤ 2 * d - c := by
  have hα1 : α < 2 / 3 := by nlinarith
  have hq : 0 < 2 - α - α ^ 2 := by nlinarith
  have hD : 0 < 4 - 4 * α - α ^ 2 := by nlinarith
  set q := 2 - α - α ^ 2 with hqdef
  set D := 4 - 4 * α - α ^ 2 with hDdef
  set d0 := D * c / q with hd0
  have hd0d : d0 ≤ d := by rw [hd0, div_le_iff₀ hq]; linarith
  have hB := boundI α c d0 x y hD
  -- value bound at d0
  have hval : 2 * (1 - α) * d0 ^ 2 ≤ D * c * (2 * d0 - c) := by
    have e : D * c * (2 * d0 - c) - 2 * (1 - α) * d0 ^ 2 =
        D * c ^ 2 * (1 - α) * (4 - 7 * α ^ 2 - α ^ 3) / q ^ 2 := by
      rw [hd0]; field_simp; ring
    have : 0 ≤ D * c ^ 2 * (1 - α) * (4 - 7 * α ^ 2 - α ^ 3) / q ^ 2 := by
      have h7 : 0 ≤ 4 - 7 * α ^ 2 - α ^ 3 := by nlinarith
      have : 0 ≤ 1 - α := by linarith
      positivity
    linarith
  have hf0 : f α c d0 x y ≤ 2 * d0 - c := by
    have : D * c * f α c d0 x y ≤ D * c * (2 * d0 - c) := le_trans hB hval
    exact le_of_mul_le_mul_left this (by positivity)
  rw [f_affine α c d d0 x y]
  have : 0 ≤ (d - d0) * (2 - (x + (α * x + (1 - α) * y))) := by
    apply mul_nonneg (by linarith)
    nlinarith
  nlinarith

/-- Corner regime, case `α² + 3α ≥ 2`. -/
theorem cornerII (α c d x y : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (hk : 0 ≤ α ^ 2 + 3 * α - 2)
    (hc : 0 < c) (hd : 2 * c ≤ (1 + α) * d)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    f α c d x y ≤ 2 * d - c := by
  have hp : 0 < 1 + α := by linarith
  set d0 := 2 * c / (1 + α) with hd0
  have hd0d : d0 ≤ d := by rw [hd0, div_le_iff₀ hp]; linarith
  have hB := boundII α c d0 x y h0 h1 hk hc hx0 hy0
  have hsq : (1 + α) ^ 2 * d0 ^ 2 = 4 * c ^ 2 := by rw [hd0]; field_simp; norm_num
  have hf0 : f α c d0 x y ≤ c := by nlinarith
  have hd0c : c ≤ 2 * d0 - c := by
    rw [hd0]
    have : c * (1 + α) ≤ 2 * c := by nlinarith
    have e : 2 * (2 * c / (1 + α)) - c = c * (3 - α) / (1 + α) := by field_simp; ring
    rw [e, le_div_iff₀ hp]
    nlinarith
  rw [f_affine α c d d0 x y]
  have : 0 ≤ (d - d0) * (2 - (x + (α * x + (1 - α) * y))) := by
    apply mul_nonneg (by linarith)
    nlinarith
  nlinarith

theorem sqrt17_lt (α : ℝ) (h0 : 0 ≤ α) (h : α < (Real.sqrt 17 - 3) / 2) : α ^ 2 + 3 * α < 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  have hs0 := Real.sqrt_nonneg 17
  nlinarith

theorem sqrt17_ge (α : ℝ) (h0 : 0 ≤ α) (h : (Real.sqrt 17 - 3) / 2 ≤ α) : 0 ≤ α ^ 2 + 3 * α - 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  have hs0 := Real.sqrt_nonneg 17
  nlinarith

end DynOpaqueCornersAux

open DynOpaque.TwoPeriod DynOpaqueCornersAux in
theorem solution (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α)
    (hreg : (α < alphaBar ∧
        (4 - 4 * α - α ^ 2) / (2 - α - α ^ 2) ≤ (vHL vH vL - cL) / (cH - cL)) ∨
      (alphaBar ≤ α ∧ α ≤ 1 ∧ 2 / (1 + α) ≤ (vHL vH vL - cL) / (cH - cL))) :
    ∀ x ∈ box, obj3 vH vL cH cL α x.1 x.2 ≤ 2 * max (vH - cH) (vL - cL) := by
  obtain ⟨hv, hcc, h0, h1, hl⟩ := hS
  rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
  simp only
  have hc : 0 < cH - cL := by linarith
  have hobj : obj3 vH vL cH cL α x y = f α (cH - cL) (vHL vH vL - cL) x y := by
    unfold obj3 f; ring
  have hM : 2 * (vHL vH vL - cL) - (cH - cL) ≤ 2 * max (vH - cH) (vL - cL) := by
    have := le_max_left (vH - cH) (vL - cL)
    have := le_max_right (vH - cH) (vL - cL)
    unfold vHL; linarith
  rw [hobj]
  refine le_trans ?_ hM
  rcases hreg with ⟨ha, hr⟩ | ⟨ha, _, hr⟩
  · have hk := sqrt17_lt α h0 ha
    have hq : 0 < 2 - α - α ^ 2 := by nlinarith
    apply cornerI α (cH - cL) (vHL vH vL - cL) x y h0 hk hc _ hx0 hx1 hy0 hy1
    rw [div_le_div_iff₀ hq hc] at hr
    linarith
  · have hk := sqrt17_ge α h0 ha
    apply cornerII α (cH - cL) (vHL vH vL - cL) x y h0 h1 hk hc _ hx0 hx1 hy0 hy1
    rw [div_le_div_iff₀ (by linarith) hc] at hr
    linarith
