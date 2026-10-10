-- Prove2me | solution 1 for BookProof.InverseTransform.cdf_monotone
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:12:22.737021+00:00
-- url     : https://prove2.me/submissions/8274fc26-467a-4509-955f-07c9d9d2fe03

-- Generated from ChapterInverseTransform.lean — solution of BookProof.InverseTransform.cdf_monotone
import Mathlib
import Definitions.Def_ChapterInverseTransform
open BookProof.InverseTransform




open MeasureTheory Set Function

variable {n : ℕ} (p : ℕ → ℝ)

variable {n : ℕ} (p : ℕ → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (hp : ∀ i, 0 ≤ p i) : Monotone (cdf p) :=
  fun _ _ hij =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij) fun i _ _ => hp i
