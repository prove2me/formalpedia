-- Prove2me | solution 1 for Formalism.BehrendSets.Rand.prob_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:34.450233+00:00
-- url     : https://prove2.me/submissions/0853fefa-2784-4ec4-ade5-c8d237f705ee

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_filter
import Theorems.Thm_Formalism_BehrendSets_Rand_wt_nonneg

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
theorem _root_.solution (X : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (P Q : Finset α → Prop)
    (hPQ : ∀ T ⊆ X, P T → Q T) : prob X δ P ≤ prob X δ Q := by
  classical
  rw [prob_filter, prob_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro T hT
    rw [mem_filter, mem_powerset] at hT ⊢
    exact ⟨hT.1, hPQ T hT.1 hT.2⟩
  · intro T _ _
    exact wt_nonneg X T h0 h1
end Formalism.BehrendSets.Rand
