-- Prove2me | solution 1 for Formalism.BehrendSets.Rand.prob_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:25.759109+00:00
-- url     : https://prove2.me/submissions/76738b0d-f1ef-4496-b2d7-03a297f7505a

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_filter
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_sub

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
theorem _root_.solution (X S : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) :
    prob X δ (fun T => S ⊆ T) ≤ δ ^ S.card := by
  by_cases hS : S ⊆ X
  · exact (prob_sub X S δ hS).le
  · have h : prob X δ (fun T => S ⊆ T) = 0 := by
      rw [prob_filter, Finset.filter_false_of_mem, Finset.sum_empty]
      intro T hT hST
      exact hS (hST.trans (mem_powerset.mp hT))
    rw [h]
    exact pow_nonneg h0 _
end Formalism.BehrendSets.Rand
