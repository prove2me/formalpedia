-- Prove2me | solution 1 for DarbouxRS.taggedSum_le_upperSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:53:51.473819+00:00
-- url     : https://prove2.me/submissions/4b734d93-3711-4eaa-9bf7-e68bf9f27a61

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

theorem solution {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    taggedSum P tags f alpha ≤ upperSum P f alpha := by
  rcases hs with ⟨hab, hfAbove, hfBelow, hmono⟩

  unfold taggedSum upperSum

  refine Finset.sum_le_sum ?_
  intro i _hi

  have hstep :
      f (tags i) ≤ upperStep P f i :=
    by
      have hcellAbove : BddAbove (f '' Partition.subinterval P i) :=
        BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hfAbove
      unfold upperStep
      exact le_csSup hcellAbove ⟨tags i, htags i, rfl⟩

  have hinc :
      0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P
      ⟨hab, hfAbove, hfBelow, hmono⟩

  exact mul_le_mul_of_nonneg_right hstep hinc
