-- Prove2me | solution 1 for Devaney.exists_continuous_period_five_not_three
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T04:51:28.376461+00:00
-- url     : https://prove2.me/submissions/1604e6ae-9a88-42ea-83d4-fe850019ab57

import Mathlib
import Definitions.Def_Devaney_sarkovskii

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Devaney

/-!
# A continuous map with a point of period five but none of period three

Mathlib has no interval dynamics.  The Stefan cycle `1 -> 3 -> 4 -> 2 -> 5 -> 1` is realised
here by an explicit piecewise-linear map written as a combination of absolute values, in a
private namespace, and the absence of period three is read off from the induced interval
transitions.
-/

namespace P5


/-- The piecewise-linear map with breakpoints `1,2,3,4,5` and values `3,5,4,2,1`. -/
noncomputable def f (x : ℝ) : ℝ :=
  2 + |x - 1| - (3 / 2) * |x - 2| - (1 / 2) * |x - 3| + (1 / 2) * |x - 4| + (1 / 2) * |x - 5|

theorem f_continuous : Continuous f := by
  unfold f
  fun_prop

theorem f_lo {x : ℝ} (h : x ≤ 1) : f x = 3 := by
  unfold f
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
    abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  ring

theorem f_12 {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : f x = 1 + 2 * x := by
  unfold f
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
    abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  ring

theorem f_23 {x : ℝ} (h1 : 2 ≤ x) (h2 : x ≤ 3) : f x = 7 - x := by
  unfold f
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith),
    abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  ring

theorem f_34 {x : ℝ} (h1 : 3 ≤ x) (h2 : x ≤ 4) : f x = 10 - 2 * x := by
  unfold f
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
    abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  ring

theorem f_45 {x : ℝ} (h1 : 4 ≤ x) (h2 : x ≤ 5) : f x = 6 - x := by
  unfold f
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
    abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  ring

theorem f_hi {x : ℝ} (h : 5 ≤ x) : f x = 1 := by
  unfold f
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
    abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  ring

/-- The range of `f` lies in `[1,5]`. -/
theorem f_mem (x : ℝ) : 1 ≤ f x ∧ f x ≤ 5 := by
  rcases le_or_gt x 1 with h | h
  · rw [f_lo h]; constructor <;> norm_num
  · rcases le_or_gt x 2 with h2 | h2
    · rw [f_12 (by linarith) h2]; constructor <;> linarith
    · rcases le_or_gt x 3 with h3 | h3
      · rw [f_23 (by linarith) h3]; constructor <;> linarith
      · rcases le_or_gt x 4 with h4 | h4
        · rw [f_34 (by linarith) h4]; constructor <;> linarith
        · rcases le_or_gt x 5 with h5 | h5
          · rw [f_45 (by linarith) h5]; constructor <;> linarith
          · rw [f_hi (by linarith)]; constructor <;> norm_num

/-- Every point of a `3`-cycle of `f` lies in `[3,4]`. -/
theorem in34 {y0 y1 y2 : ℝ} (h01 : f y0 = y1) (h12 : f y1 = y2) (h20 : f y2 = y0) :
    3 ≤ y0 ∧ y0 ≤ 4 := by
  have m0 := f_mem y2
  rw [h20] at m0
  have m1 := f_mem y0
  rw [h01] at m1
  have m2 := f_mem y1
  rw [h12] at m2
  obtain ⟨l0, u0⟩ := m0
  obtain ⟨l1, u1⟩ := m1
  obtain ⟨l2, u2⟩ := m2
  by_contra hcon
  rcases le_or_gt y0 2 with c1 | c1
  · -- y0 ∈ [1,2]
    rw [f_12 l0 c1] at h01
    rcases le_or_gt y1 4 with d1 | d1
    · rw [f_34 (by linarith) d1] at h12
      rcases le_or_gt y2 3 with e1 | e1
      · rw [f_23 (by linarith) e1] at h20
        linarith
      · rw [f_34 (by linarith) (by linarith)] at h20
        linarith
    · rw [f_45 (by linarith) u1] at h12
      rw [f_12 (by linarith) (by linarith)] at h20
      linarith
  · rcases le_or_gt y0 3 with c2 | c2
    · rw [f_23 (by linarith) c2] at h01
      rw [f_45 (by linarith) (by linarith)] at h12
      rw [f_12 (by linarith) (by linarith)] at h20
      linarith
    · rcases le_or_gt y0 4 with c3 | c3
      · exact hcon ⟨by linarith, c3⟩
      · -- y0 ∈ [4,5]
        rw [f_45 (by linarith) u0] at h01
        rw [f_12 (by linarith) (by linarith)] at h12
        rcases le_or_gt y2 4 with e1 | e1
        · rw [f_34 (by linarith) e1] at h20
          linarith
        · rw [f_45 (by linarith) (by linarith)] at h20
          linarith

theorem no_period_three {x : ℝ} (h : f^[3] x = x) : f x = x := by
  have h3 : f (f (f x)) = x := by
    simpa [Function.iterate_succ_apply, Function.iterate_succ_apply'] using h
  have a0 : 3 ≤ x ∧ x ≤ 4 := in34 rfl rfl h3
  have a1 : 3 ≤ f x ∧ f x ≤ 4 := in34 rfl h3 rfl
  have a2 : 3 ≤ f (f x) ∧ f (f x) ≤ 4 := in34 h3 rfl rfl
  have e0 : f x = 10 - 2 * x := f_34 a0.1 a0.2
  have e1 : f (f x) = 10 - 2 * (f x) := f_34 a1.1 a1.2
  have e2 : f (f (f x)) = 10 - 2 * (f (f x)) := f_34 a2.1 a2.2
  rw [h3] at e2
  rw [e0]
  linarith [e0, e1, e2]

theorem f1 : f 1 = 3 := by rw [f_12 (le_refl 1) (by norm_num)]; norm_num
theorem f3 : f 3 = 4 := by rw [f_34 (le_refl 3) (by norm_num)]; norm_num
theorem f4 : f 4 = 2 := by rw [f_45 (le_refl 4) (by norm_num)]; norm_num
theorem f2 : f 2 = 5 := by rw [f_23 (by norm_num) (by norm_num)]; norm_num
theorem f5 : f 5 = 1 := by rw [f_45 (by norm_num) (le_refl 5)]; norm_num

theorem period5 : HasPrimePeriod f 1 5 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · show f^[5] (1 : ℝ) = 1
    norm_num [Function.iterate_succ_apply, f1, f3, f4, f2, f5]
  · intro m hm0 hm5
    interval_cases m <;>
      norm_num [Function.iterate_succ_apply, f1, f3, f4, f2, f5]

theorem main : ∃ g : ℝ → ℝ, Continuous g ∧ (∃ x, HasPrimePeriod g x 5)
    ∧ ¬ ∃ x, HasPrimePeriod g x 3 := by
  refine ⟨f, f_continuous, ⟨1, period5⟩, ?_⟩
  rintro ⟨x, -, h3, hlt⟩
  exact hlt 1 (by norm_num) (by norm_num) (no_period_three h3)


end P5

theorem solution :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∃ x, Devaney.HasPrimePeriod f x 5)
      ∧ ¬ ∃ x, Devaney.HasPrimePeriod f x 3 :=
  P5.main
