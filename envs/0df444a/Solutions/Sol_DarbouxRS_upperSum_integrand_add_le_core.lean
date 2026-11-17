-- Prove2me | solution 1 for DarbouxRS.upperSum_integrand_add_le_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:47:10.518935+00:00
-- url     : https://prove2.me/submissions/cde1ec82-7cbc-4841-be3a-c4093fdc9546

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic
import Theorems.Thm_DarbouxRS_upperStep_integrand_add_le_core
import Theorems.Thm_DarbouxRS_partition_increment_nonneg_of_source_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DarbouxRS
open scoped BigOperators Pointwise
noncomputable section

theorem solution {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    upperSum P (fun x => f x + g x) alpha ≤
      upperSum P f alpha + upperSum P g alpha := by
  rcases hsf with ⟨_hab, hfAbove, _hfBelow, _hmono⟩
  rcases hsg with ⟨_habg, hgAbove, _hgBelow, _hmonog⟩
  unfold upperSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- `i` is explicitly passed
  have hstep := upperStep_integrand_add_le_core P i hfAbove hgAbove

  -- Reconstruct the SourceHypotheses on the fly using the pieces in your context!
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P ⟨_hab, hfAbove, _hfBelow, _hmono⟩

  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith
