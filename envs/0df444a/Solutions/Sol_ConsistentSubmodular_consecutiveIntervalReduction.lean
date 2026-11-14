-- Prove2me | solution 1 for ConsistentSubmodular.consecutiveIntervalReduction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:46:06.639085+00:00
-- url     : https://prove2.me/submissions/8dfec443-002f-4205-8efb-c72d8a718a31

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ShadowIntervals
import Theorems.Thm_ConsistentSubmodular_Shadow_shadow_bound

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Shadow

variable {N : ℕ} (I : IntervalInstance N)

theorem left_le_hindsight (j : Fin (N + 1)) : I.left j ≤ hindsight I j :=
  (le_add_of_nonneg_right (le_max_left _ _)).trans
    (Finset.le_sup' (fun i => I.value i j) (Finset.mem_univ j))

end ConsistentSubmodular.Shadow

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Shadow

theorem adaptiveValue_nonneg {N : ℕ} (I : IntervalInstance N) : 0 ≤ I.adaptiveValue :=
  Finset.sum_nonneg fun j _ =>
    mul_nonneg (I.prob_nonneg j) ((I.left_nonneg j).trans (left_le_hindsight I j))

/-- **Lemma 3** (reduction to consecutive intervals). -/
theorem consecutiveIntervalReduction : ConsecutiveIntervalReductionGoal := by
  intro α hα0 hα1 hchain N I
  rw [IntervalInstance.adaptivityGap]
  split_ifs with h0
  · exact hα1
  · rw [le_div_iff₀ (lt_of_le_of_ne (adaptiveValue_nonneg I) (Ne.symm h0))]
    exact shadow_bound I hα0 hα1 hchain

end ConsistentSubmodular.Shadow

end

end

section

open ConsistentSubmodular

theorem solution : ConsecutiveIntervalReductionGoal :=
  Shadow.consecutiveIntervalReduction

end
