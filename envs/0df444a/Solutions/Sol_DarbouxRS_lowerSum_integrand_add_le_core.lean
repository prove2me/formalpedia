-- Prove2me | solution 1 for DarbouxRS.lowerSum_integrand_add_le_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:47:03.070872+00:00
-- url     : https://prove2.me/submissions/e178084a-95f6-4aa6-8961-827ed15e587c

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic
import Theorems.Thm_DarbouxRS_lowerStep_integrand_add_le_core
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
    lowerSum P f alpha + lowerSum P g alpha ≤
      lowerSum P (fun x => f x + g x) alpha := by
  -- For lower sums, we need the `BddBelow` pieces!
  rcases hsf with ⟨_hab, _hfAbove, hfBelow, _hmono⟩
  rcases hsg with ⟨_habg, _hgAbove, hgBelow, _hmonog⟩
  unfold lowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- Apply the lowerStep lemma we fixed earlier
  have hstep := lowerStep_integrand_add_le_core P i hfBelow hgBelow

  -- Reconstruct the SourceHypotheses for the increment proof
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) := by
    exact partition_increment_nonneg_of_source_core P
      ⟨_hab, _hfAbove, hfBelow, _hmono⟩

  -- Multiply the step inequality by the non-negative increment width
  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith
