-- Prove2me | solution 1 for BookProof.ChapterOrthogonalSums.summable_of_orthogonal_of_summable_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:22.604338+00:00
-- url     : https://prove2.me/submissions/0700597d-eef5-418d-a9bb-e1fb9bc7e83a

-- Generated from ChapterOrthogonalSums.lean — solution of BookProof.ChapterOrthogonalSums.summable_of_orthogonal_of_summable_norm_sq
import Mathlib
import Definitions.Def_ChapterOrthogonalSums
import Theorems.Thm_BookProof_ChapterOrthogonalSums_norm_sum_sq_of_orthogonal
open BookProof.ChapterOrthogonalSums



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace E] {ι : Type*} {v : ι → E}
    (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) (hsum : Summable fun x => ‖v x‖ ^ 2) :
    Summable v := by

  rw [summable_iff_vanishing]
  intro e he
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 he
  have hε2 : 0 < ε ^ 2 := by positivity
  obtain ⟨t₀, ht₀⟩ :=
    (summable_iff_vanishing.1 hsum) (Metric.ball 0 (ε ^ 2)) (Metric.ball_mem_nhds 0 hε2)
  refine ⟨t₀, fun t ht => hball ?_⟩
  have hnn : (0 : ℝ) ≤ ∑ x ∈ t, ‖v x‖ ^ 2 := Finset.sum_nonneg fun x _ => by positivity
  have h1 : ∑ x ∈ t, ‖v x‖ ^ 2 < ε ^ 2 := by
    have h := ht₀ t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h
    exact h
  have h2 : ‖∑ x ∈ t, v x‖ ^ 2 < ε ^ 2 := by
    rw [norm_sum_sq_of_orthogonal _ horth]
    exact h1
  rw [Metric.mem_ball, dist_zero_right]
  nlinarith [norm_nonneg (∑ x ∈ t, v x), hε]
