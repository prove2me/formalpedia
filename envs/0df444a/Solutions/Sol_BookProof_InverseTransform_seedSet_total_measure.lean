-- Prove2me | solution 1 for BookProof.InverseTransform.seedSet_total_measure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:13:19.331833+00:00
-- url     : https://prove2.me/submissions/dfbd78aa-95d0-4ac2-85b9-c5f9c539c6df

-- Generated from ChapterInverseTransform.lean — solution of BookProof.InverseTransform.seedSet_total_measure
import Mathlib
import Definitions.Def_ChapterInverseTransform
import Theorems.Thm_BookProof_InverseTransform_seedSet_measure
open BookProof.InverseTransform




open MeasureTheory Set Function

variable {n : ℕ} (p : ℕ → ℝ)

variable {n : ℕ} (p : ℕ → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (hp : ∀ i, 0 ≤ p i) (hsum : cdf p n = 1) :
    ∑ k ∈ Finset.range n, volume (seedSet p k) = 1 := by

  rw [Finset.sum_congr rfl fun k _ => seedSet_measure p k,
    ← ENNReal.ofReal_sum_of_nonneg fun i _ => hp i]
  have : ∑ i ∈ Finset.range n, p i = 1 := hsum
  rw [this, ENNReal.ofReal_one]
