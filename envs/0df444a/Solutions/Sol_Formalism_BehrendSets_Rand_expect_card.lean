-- Prove2me | solution 1 for Formalism.BehrendSets.Rand.expect_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:31:54.772047+00:00
-- url     : https://prove2.me/submissions/5b306c40-6ef2-4376-9e28-6cb41357fe29

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_eq_sum_ite
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
theorem _root_.solution (X : Finset α) (δ : ℝ) :
    expect X δ (fun T => (T.card : ℝ)) = δ * X.card := by
  unfold expect
  have h1 : ∀ T ∈ X.powerset,
      wt X δ T * (T.card : ℝ) = ∑ x ∈ X, if x ∈ T then wt X δ T else 0 := by
    intro T hT
    rw [Finset.sum_ite_mem, inter_eq_right.mpr (mem_powerset.mp hT), Finset.sum_const,
      nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ x ∈ X, (∑ T ∈ X.powerset, if x ∈ T then wt X δ T else 0) = δ := by
    intro x hx
    calc (∑ T ∈ X.powerset, if x ∈ T then wt X δ T else 0)
        = prob X δ (fun T => {x} ⊆ T) := by
          rw [prob_eq_sum_ite]
          refine Finset.sum_congr rfl fun T _ => ?_
          by_cases h : x ∈ T
          · rw [if_pos h, if_pos (singleton_subset_iff.mpr h)]
          · rw [if_neg h, if_neg (fun h' => h (singleton_subset_iff.mp h'))]
      _ = δ := by rw [prob_sub X {x} δ (singleton_subset_iff.mpr hx), card_singleton, pow_one]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, mul_comm]
end Formalism.BehrendSets.Rand
