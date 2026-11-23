-- Prove2me | solution 1 for Formalism.BehrendSets.Rand.prob_exists_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:34.391932+00:00
-- url     : https://prove2.me/submissions/bd37c78d-885f-4436-ab04-eb60beba48ed

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_eq_sum_ite
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
theorem _root_.solution {ι : Type} (X : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (J : Finset ι) (E : ι → Finset α → Prop) :
    prob X δ (fun T => ∃ j ∈ J, E j T) ≤ ∑ j ∈ J, prob X δ (E j) := by
  classical
  rw [prob_eq_sum_ite X δ (fun T => ∃ j ∈ J, E j T),
    Finset.sum_congr rfl (fun j _ => prob_eq_sum_ite X δ (E j)), Finset.sum_comm]
  apply Finset.sum_le_sum
  intro T _
  have hnn : ∀ i ∈ J, 0 ≤ (if E i T then wt X δ T else 0) := by
    intro i _
    by_cases h : E i T
    · rw [if_pos h]; exact wt_nonneg X T h0 h1
    · rw [if_neg h]
  by_cases h : ∃ j ∈ J, E j T
  · rw [if_pos h]
    obtain ⟨j, hj, hE⟩ := h
    calc wt X δ T = (if E j T then wt X δ T else 0) := by rw [if_pos hE]
      _ ≤ ∑ i ∈ J, (if E i T then wt X δ T else 0) :=
        Finset.single_le_sum (f := fun i => if E i T then wt X δ T else 0) hnn hj
  · rw [if_neg h]
    exact Finset.sum_nonneg hnn
end Formalism.BehrendSets.Rand
