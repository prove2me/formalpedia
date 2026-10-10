-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.norm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:49.089597+00:00
-- url     : https://prove2.me/submissions/95a36b8f-a164-41be-abd3-dfcef8fe1281

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.norm_term_le
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_norm_pow_le_of_numRadiusLE
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace E] {A : E →L[ℂ] E} {r M R : ℝ} (hr : 0 ≤ r)
    (hM : 0 ≤ M) (hR : r < R) (h : NumRadiusLE A r) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ M / R ^ n) (n : ℕ) (hn : 0 < n) :
    ‖a n • A ^ n‖ ≤ 2 * M * (r / R) ^ n := by

  have hR0 : 0 < R := lt_of_le_of_lt hr hR
  have hRn : 0 < R ^ n := by positivity
  have h1 : ‖a n • A ^ n‖ = ‖a n‖ * ‖A ^ n‖ := by rw [norm_smul]
  rw [h1]
  have h2 : ‖A ^ n‖ ≤ 2 * r ^ n := norm_pow_le_of_numRadiusLE hr h n hn
  have h3 : ‖a n‖ ≤ M / R ^ n := ha n
  have h4 : (0:ℝ) ≤ ‖A ^ n‖ := norm_nonneg _
  have h5 : ‖a n‖ * ‖A ^ n‖ ≤ (M / R ^ n) * (2 * r ^ n) := by
    apply mul_le_mul h3 h2 h4
    positivity
  calc ‖a n‖ * ‖A ^ n‖ ≤ (M / R ^ n) * (2 * r ^ n) := h5
    _ = 2 * M * (r / R) ^ n := by
        rw [div_pow]
        field_simp
