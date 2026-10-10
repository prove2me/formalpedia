-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.crouzeix_disc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:52.087019+00:00
-- url     : https://prove2.me/submissions/0b12ef46-7600-4845-a785-e0d891bedd28

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.crouzeix_disc
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_norm_term_le
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_summable_analyticFC
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace E] {A : E →L[ℂ] E} {r M R : ℝ} (hr : 0 ≤ r)
    (hM : 0 ≤ M) (hR : r < R) (h : NumRadiusLE A r) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ M / R ^ n) :
    ‖analyticFC a A‖ ≤ (1 + 2 * r / (R - r)) * M := by

  have hR0 : 0 < R := lt_of_le_of_lt hr hR
  have hRr : (0:ℝ) < R - r := by linarith
  have hq0 : 0 ≤ r / R := by positivity
  have hq1 : r / R < 1 := (div_lt_one hR0).mpr hR
  have hsum : Summable fun n : ℕ => a n • A ^ n := summable_analyticFC hr hM hR h ha
  have hhead : ‖a 0 • A ^ 0‖ ≤ M := by
    have h2 : ‖a 0‖ ≤ M := by simpa using ha 0
    have hone : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := by
      rw [show (1 : E →L[ℂ] E) = ContinuousLinearMap.id ℂ E from rfl]
      exact ContinuousLinearMap.norm_id_le
    have h1 : ‖a 0 • A ^ 0‖ ≤ ‖a 0‖ := by
      rw [norm_smul, pow_zero]
      nlinarith [norm_nonneg (a 0), norm_nonneg (1 : E →L[ℂ] E)]
    linarith
  have hsplit : analyticFC a A = a 0 • A ^ 0 + ∑' n : ℕ, a (n + 1) • A ^ (n + 1) := by
    rw [analyticFC, hsum.tsum_eq_zero_add]
  have hgeo : HasSum (fun n : ℕ => (2 * M * (r / R)) * (r / R) ^ n)
      ((2 * M * (r / R)) * (1 - r / R)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left _
  have hval : (2 * M * (r / R)) * (1 - r / R)⁻¹ = 2 * M * (r / (R - r)) := by
    have h1 : (1 : ℝ) - r / R = (R - r) / R := by field_simp
    rw [h1]
    field_simp
  rw [hval] at hgeo
  have htail : ‖∑' n : ℕ, a (n + 1) • A ^ (n + 1)‖ ≤ 2 * M * (r / (R - r)) := by
    refine tsum_of_norm_bounded hgeo fun n => ?_
    refine le_trans (norm_term_le hr hM hR h ha (n + 1) (Nat.succ_pos n)) ?_
    rw [pow_succ]
    ring_nf
    exact le_of_eq (by ring)
  rw [hsplit]
  calc ‖a 0 • A ^ 0 + ∑' n : ℕ, a (n + 1) • A ^ (n + 1)‖
      ≤ ‖a 0 • A ^ 0‖ + ‖∑' n : ℕ, a (n + 1) • A ^ (n + 1)‖ := norm_add_le _ _
    _ ≤ M + 2 * M * (r / (R - r)) := by linarith
    _ = (1 + 2 * r / (R - r)) * M := by field_simp
