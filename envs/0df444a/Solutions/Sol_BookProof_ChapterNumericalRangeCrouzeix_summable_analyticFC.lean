-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.summable_analyticFC
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:50.630262+00:00
-- url     : https://prove2.me/submissions/9786a6c2-0b14-4472-be72-3a84a08226ff

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.summable_analyticFC
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_norm_term_le
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace E] {A : E →L[ℂ] E} {r M R : ℝ} (hr : 0 ≤ r)
    (hM : 0 ≤ M) (hR : r < R) (h : NumRadiusLE A r) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ M / R ^ n) : Summable fun n : ℕ => a n • A ^ n := by

  have hR0 : 0 < R := lt_of_le_of_lt hr hR
  have hq0 : 0 ≤ r / R := by positivity
  have hq1 : r / R < 1 := (div_lt_one hR0).mpr hR
  have hgeo : Summable fun n : ℕ => 2 * M * (r / R) ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  refine Summable.of_norm_bounded hgeo ?_
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h2 : ‖a 0‖ ≤ M := by simpa using ha 0
    have hone : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := by
      rw [show (1 : E →L[ℂ] E) = ContinuousLinearMap.id ℂ E from rfl]
      exact ContinuousLinearMap.norm_id_le
    have h1 : ‖a 0 • A ^ 0‖ ≤ ‖a 0‖ := by
      rw [norm_smul, pow_zero]
      nlinarith [norm_nonneg (a 0), norm_nonneg (1 : E →L[ℂ] E)]
    calc ‖a 0 • A ^ 0‖ ≤ M := le_trans h1 h2
      _ ≤ 2 * M * (r / R) ^ 0 := by simp; linarith
  · exact norm_term_le hr hM hR h ha n hn
