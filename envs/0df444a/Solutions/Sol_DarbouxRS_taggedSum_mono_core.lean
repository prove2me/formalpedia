-- Prove2me | solution 1 for DarbouxRS.taggedSum_mono_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:49:20.10121+00:00
-- url     : https://prove2.me/submissions/ba3d53b7-4d5d-4ca3-9bb6-6e809576ddde

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic
import Theorems.Thm_DarbouxRS_partition_increment_nonneg_of_source_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DarbouxRS
open scoped BigOperators Pointwise
noncomputable section

theorem solution {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    {f g alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (htags : tagsInPartition P tags)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    taggedSum P tags f alpha ≤ taggedSum P tags g alpha := by
  unfold taggedSum
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- 1. Prove the tag is inside [a, b]
  have htag : tags i ∈ Set.Icc a b := subinterval_subset_Icc_core P (htags i)

  -- 2. Evaluate the function inequality at the tag
  have hstep : f (tags i) ≤ g (tags i) := hfg (tags i) htag

  -- 3. The increment is non-negative (pass `hs` directly!)
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P hs

  -- 4. Multiply the step inequality by the non-negative increment
  exact mul_le_mul_of_nonneg_right hstep hinc
