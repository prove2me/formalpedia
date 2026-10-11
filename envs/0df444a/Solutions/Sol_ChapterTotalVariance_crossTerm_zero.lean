-- Prove2me | solution 1 for ChapterTotalVariance.crossTerm_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:07.429429+00:00
-- url     : https://prove2.me/submissions/6dd72d45-5f5f-4d93-8f4a-4b40ab72e429

-- Generated from ChapterTotalVariance.lean — solution of ChapterTotalVariance.crossTerm_zero
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Theorems.Thm_ChapterTotalVariance_groupBalance
import Definitions.Def_ChapterA4
open ChapterTotalVariance




open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

set_option maxHeartbeats 1000000 in
theorem solution [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) :
    (∑ ω, w ω * (Y ω - condMean w X Y (X ω)) * (condMean w X Y (X ω) - mean w Y))
      = 0 := by

  letI := Fintype.ofFinite κ
  -- Regroup the sum over `ω` by the group value `g = X ω` using `Finset.sum_ite_eq`
  -- to introduce an inner sum over `g`, then swap and factor out `(condMean g - mean)`
  -- from each fiber; the remaining fiber sum is `groupBalance`, which is `0`.
  have key : ∀ ω, w ω * (Y ω - condMean w X Y (X ω)) * (condMean w X Y (X ω) - mean w Y)
      = ∑ g, if X ω = g then
          (condMean w X Y g - mean w Y) * (w ω * (Y ω - condMean w X Y g)) else 0 := by
    intro ω
    rw [Finset.sum_ite_eq Finset.univ (X ω)
      (fun g => (condMean w X Y g - mean w Y) * (w ω * (Y ω - condMean w X Y g)))]
    simp only [Finset.mem_univ, if_true]
    ring
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun g _ => ?_)
  have : (∑ ω, if X ω = g then
      (condMean w X Y g - mean w Y) * (w ω * (Y ω - condMean w X Y g)) else 0)
      = (condMean w X Y g - mean w Y) *
        (∑ ω, if X ω = g then w ω * (Y ω - condMean w X Y g) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases h : X ω = g <;> simp [h]
  rw [this, groupBalance w X Y hw g, mul_zero]
