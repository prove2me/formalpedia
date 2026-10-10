-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.crouzeix_ball
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:56.445687+00:00
-- url     : https://prove2.me/submissions/a557b960-a26e-40e4-9387-3eabaa84027d

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.crouzeix_ball
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_crouzeix_disc
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace E] {A : E →L[ℂ] E} {c : ℂ} {r M R : ℝ} (hr : 0 ≤ r)
    (hM : 0 ≤ M) (hR : r < R) (h : NumBallLE A c r) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ M / R ^ n) :
    ‖analyticFC a (A - c • (1 : E →L[ℂ] E))‖ ≤ (1 + 2 * r / (R - r)) * M := crouzeix_disc hr hM hR h ha
