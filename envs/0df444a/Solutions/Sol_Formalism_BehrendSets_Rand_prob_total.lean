-- Prove2me | solution 1 for Formalism.BehrendSets.Rand.prob_total
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:35.051533+00:00
-- url     : https://prove2.me/submissions/e2910502-c886-4592-aca0-147fb523a8ac

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_filter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Rand
variable {α : Type} [DecidableEq α]
namespace Formalism.BehrendSets.Rand
theorem _root_.solution (X : Finset α) (δ : ℝ) : prob X δ (fun _ => True) = 1 := by
  rw [prob_filter]
  rw [filter_true_of_mem (fun _ _ => trivial)]
  have h : ∀ T ∈ X.powerset, wt X δ T = δ ^ T.card * (1 - δ) ^ (X.card - T.card) := by
    intro T hT
    unfold wt
    rw [card_sdiff_of_subset (mem_powerset.mp hT)]
  rw [Finset.sum_congr rfl h, Finset.sum_pow_mul_eq_add_pow, add_sub_cancel, one_pow]
end Formalism.BehrendSets.Rand
