-- Prove2me | solution 1 for Formalism.BehrendSets.Rand.prob_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:57.185882+00:00
-- url     : https://prove2.me/submissions/9035be72-7001-4846-a851-a63cbddc42e6

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_filter
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_total
import Theorems.Thm_Formalism_BehrendSets_Rand_wt_union

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
theorem _root_.solution (X S : Finset α) (δ : ℝ) (hS : S ⊆ X) :
    prob X δ (fun T => S ⊆ T) = δ ^ S.card := by
  symm
  calc δ ^ S.card = δ ^ S.card * prob (X \ S) δ (fun _ => True) := by
        rw [prob_total, mul_one]
    _ = ∑ U ∈ (X \ S).powerset, δ ^ S.card * wt (X \ S) δ U := by
        rw [prob_filter, filter_true_of_mem (fun _ _ => trivial), Finset.mul_sum]
    _ = prob X δ (fun T => S ⊆ T) := by
        rw [prob_filter]
        symm
        refine Finset.sum_nbij' (fun T => T \ S) (fun U => S ∪ U) ?_ ?_ ?_ ?_ ?_
        · intro T hT
          rw [mem_filter, mem_powerset] at hT
          rw [mem_powerset]
          intro x hx
          rw [mem_sdiff] at hx ⊢
          exact ⟨hT.1 hx.1, hx.2⟩
        · intro U hU
          rw [mem_powerset] at hU
          rw [mem_filter, mem_powerset]
          exact ⟨union_subset hS (hU.trans sdiff_subset), subset_union_left⟩
        · intro T hT
          rw [mem_filter] at hT
          exact union_sdiff_of_subset hT.2
        · intro U hU
          rw [mem_powerset] at hU
          ext x
          have hx := @hU x
          simp only [mem_sdiff, mem_union] at hx ⊢
          tauto
        · intro T hT
          rw [mem_filter, mem_powerset] at hT
          have hU : T \ S ⊆ X \ S := by
            intro x hx
            rw [mem_sdiff] at hx ⊢
            exact ⟨hT.1 hx.1, hx.2⟩
          rw [← wt_union X S (T \ S) δ hU, union_sdiff_of_subset hT.2]
end Formalism.BehrendSets.Rand
