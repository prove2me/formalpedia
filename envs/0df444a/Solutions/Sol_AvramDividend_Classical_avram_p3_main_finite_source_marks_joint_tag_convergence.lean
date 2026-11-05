-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_finite_source_marks_joint_tag_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:06:47.43324+00:00
-- url     : https://prove2.me/submissions/97518e38-8165-4722-9564-192a37317fcd

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped NNReal

/-- All chosen finite original BV source marks have uniformly accurate left
and right grid tags once their individual tags converge to the same time. -/
theorem solution
    {ι : Type*} (S : Finset ι) (t : ι → ℝ≥0)
    (leftTag rightTag : ℕ → ι → ℝ≥0)
    (hleft : ∀ i, Tendsto (fun n => leftTag n i) atTop (nhds (t i)))
    (hright : ∀ i, Tendsto (fun n => rightTag n i) atTop (nhds (t i)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ S,
      dist (leftTag n i) (t i) < ε ∧
      dist (rightTag n i) (t i) < ε := by
  classical
  have hmark (i : ι) :
      ∀ᶠ n : ℕ in atTop,
        dist (leftTag n i) (t i) < ε ∧
        dist (rightTag n i) (t i) < ε := by
    have hl := (hleft i).eventually (Metric.ball_mem_nhds (t i) hε)
    have hr := (hright i).eventually (Metric.ball_mem_nhds (t i) hε)
    filter_upwards [hl, hr] with n hnl hnr
    constructor
    · simpa only [Metric.mem_ball, dist_comm] using hnl
    · simpa only [Metric.mem_ball, dist_comm] using hnr
  have hall (F : Finset ι) :
      ∀ᶠ n : ℕ in atTop, ∀ i ∈ F,
        dist (leftTag n i) (t i) < ε ∧
        dist (rightTag n i) (t i) < ε := by
    induction F using Finset.induction_on with
    | empty =>
        exact Filter.Eventually.of_forall (by intro n i hi; simp at hi)
    | @insert a F ha ih =>
        filter_upwards [hmark a, ih] with n hna hnF
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hna
        · exact hnF i hi
  exact hall S
