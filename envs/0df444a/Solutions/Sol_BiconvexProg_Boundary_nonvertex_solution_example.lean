-- Prove2me | solution 1 for BiconvexProg.Boundary.nonvertex_solution_example
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:48:56.238605+00:00
-- url     : https://prove2.me/submissions/cb34c5c4-feb6-4631-add2-d1bef0c6354f

import Mathlib

set_option autoImplicit false

namespace P4fb79572

lemma lower (x y : ℝ) (h1 : -6 * x + 8 * y ≤ 3) (h2 : 3 * x - y ≤ 3) (h3 : 0 ≤ x)
    (h5 : 0 ≤ y) : -13 / 12 ≤ -x + x * y - y := by
  rcases le_total x 1 with hx | hx <;> rcases le_total y 1 with hy | hy
  · nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hy)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hx) (by linarith : (0:ℝ) ≤ 3 + 6 * x - 8 * y),
      sq_nonneg (x - 11 / 12)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hx) (by linarith : (0:ℝ) ≤ 3 - 3 * x + y),
      sq_nonneg (x - 7 / 6)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hy)]

lemma eq_of (x y : ℝ) (h1 : -6 * x + 8 * y ≤ 3) (h2 : 3 * x - y ≤ 3) (h3 : 0 ≤ x)
    (h5 : 0 ≤ y) (h : -x + x * y - y ≤ -13 / 12) : x = 7 / 6 ∧ y = 1 / 2 := by
  have hx : 1 ≤ x := by
    by_contra hx
    push_neg at hx
    rcases le_total y 1 with hy | hy
    · nlinarith [mul_nonneg (sub_nonneg.2 hx.le) (sub_nonneg.2 hy)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hx.le) (by linarith : (0:ℝ) ≤ 3 + 6 * x - 8 * y),
        sq_nonneg (x - 11 / 12)]
  have hy : y ≤ 1 := by
    by_contra hy
    push_neg at hy
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hy.le)]
  have hsq : (x - 7 / 6) ^ 2 = 0 :=
    le_antisymm (by nlinarith [mul_nonneg (sub_nonneg.2 hx) (by linarith : (0:ℝ) ≤ 3 - 3 * x + y)])
      (sq_nonneg _)
  have hx' : x = 7 / 6 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    linarith
  subst hx'
  constructor
  · rfl
  · nlinarith

end P4fb79572

theorem solution :
    let T : Set (ℝ × ℝ) := {z | -6 * z.1 + 8 * z.2 ≤ 3 ∧ 3 * z.1 - z.2 ≤ 3 ∧
      0 ≤ z.1 ∧ z.1 ≤ 5 ∧ 0 ≤ z.2 ∧ z.2 ≤ 5}
    let f : ℝ × ℝ → ℝ := fun z => -z.1 + z.1 * z.2 - z.2
    ((7 / 6 : ℝ), (1 / 2 : ℝ)) ∈ T ∧ IsMinOn f T ((7 / 6 : ℝ), (1 / 2 : ℝ)) ∧
      ((7 / 6 : ℝ), (1 / 2 : ℝ)) ∉ Set.extremePoints ℝ T ∧
      ∀ z ∈ Set.extremePoints ℝ T, ¬ IsMinOn f T z := by
  intro T f
  have hmem : ((7 / 6 : ℝ), (1 / 2 : ℝ)) ∈ T := by
    simp only [T, Set.mem_setOf_eq]; norm_num
  have hnot : ((7 / 6 : ℝ), (1 / 2 : ℝ)) ∉ Set.extremePoints ℝ T := by
    intro h
    rw [mem_extremePoints] at h
    have m1 : ((1 : ℝ), (0 : ℝ)) ∈ T := by simp only [T, Set.mem_setOf_eq]; norm_num
    have m2 : ((4 / 3 : ℝ), (1 : ℝ)) ∈ T := by simp only [T, Set.mem_setOf_eq]; norm_num
    have hs : ((7 / 6 : ℝ), (1 / 2 : ℝ)) ∈ openSegment ℝ ((1 : ℝ), (0 : ℝ)) ((4 / 3 : ℝ), (1 : ℝ)) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by ext <;> simp <;> norm_num⟩
    have := (h.2 _ m1 _ m2 hs).1
    have := congrArg Prod.fst this
    norm_num at this
  have hmin : IsMinOn f T ((7 / 6 : ℝ), (1 / 2 : ℝ)) := by
    intro z hz
    simp only [T, Set.mem_setOf_eq] at hz
    obtain ⟨h1, h2, h3, -, h5, -⟩ := hz
    show f ((7 / 6 : ℝ), (1 / 2 : ℝ)) ≤ f z
    simp only [f]
    have := P4fb79572.lower z.1 z.2 h1 h2 h3 h5
    norm_num
    linarith
  refine ⟨hmem, hmin, hnot, ?_⟩
  intro z hz hzmin
  have hzT : z ∈ T := hz.1
  have hle := hzmin hmem
  have hzT' := hzT
  simp only [T, Set.mem_setOf_eq] at hzT'
  obtain ⟨h1, h2, h3, -, h5, -⟩ := hzT'
  have hle' : -z.1 + z.1 * z.2 - z.2 ≤ -13 / 12 := by
    have : f z ≤ f ((7 / 6 : ℝ), (1 / 2 : ℝ)) := hle
    simp only [f] at this
    norm_num at this
    linarith
  obtain ⟨e1, e2⟩ := P4fb79572.eq_of z.1 z.2 h1 h2 h3 h5 hle'
  have hzeq : z = ((7 / 6 : ℝ), (1 / 2 : ℝ)) := Prod.ext e1 e2
  exact hnot (hzeq ▸ hz)
