-- Prove2me | solution 1 for Formalism.BehrendSets.Rand.expect_sum_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:15:22.586215+00:00
-- url     : https://prove2.me/submissions/5963c2e3-9912-4df0-8e47-44a31e634a52

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_eq_sum_ite

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
theorem _root_.solution {ι : Type} (X : Finset α) (δ : ℝ) (I : Finset ι) (c : ι → ℝ)
    (E : ι → Finset α → Prop) (dec : ∀ i, DecidablePred (E i)) :
    expect X δ (fun T => ∑ i ∈ I, c i * (if E i T then 1 else 0))
      = ∑ i ∈ I, c i * prob X δ (E i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prob_eq_sum_ite X δ (E i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h : E i T
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring
end Formalism.BehrendSets.Rand
