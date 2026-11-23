-- Prove2me | solution 1 for Formalism.BehrendSets.Select.moments
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:57.502924+00:00
-- url     : https://prove2.me/submissions/2670e83d-6cc1-4dc8-ab4a-69116b3cd4a5

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_Select
import Theorems.Thm_Formalism_BehrendSets_Select_step

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
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Select
variable {α : Type} [DecidableEq α]
namespace Formalism.BehrendSets.Select
theorem _root_.solution (X : Finset α) (δ : ℝ) :
    (∑ T ∈ X.powerset, wt X δ T * 1 = 1) ∧
    (∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) = δ * X.card) ∧
    (∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) ^ 2 =
      δ * X.card * (1 - δ) + δ ^ 2 * (X.card : ℝ) ^ 2) := by
  induction X using Finset.induction_on with
  | empty => simp [wt]
  | insert a X ha ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    rw [step X δ ha, step X δ ha, step X δ ha, Finset.card_insert_of_notMem ha]
    have e0 : ∑ T ∈ X.powerset, wt X δ T * ((1 - δ) * 1 + δ * 1) =
        ∑ T ∈ X.powerset, wt X δ T * 1 := by
      apply Finset.sum_congr rfl
      intro T _
      ring
    have e1 : ∑ T ∈ X.powerset, wt X δ T *
          ((1 - δ) * ((T.card : ℕ) : ℝ) + δ * (((insert a T).card : ℕ) : ℝ)) =
        ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) + δ * ∑ T ∈ X.powerset, wt X δ T * 1 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
      rw [Finset.card_insert_of_notMem haT]
      push_cast
      ring
    have e2 : ∑ T ∈ X.powerset, wt X δ T *
          ((1 - δ) * ((T.card : ℕ) : ℝ) ^ 2 + δ * (((insert a T).card : ℕ) : ℝ) ^ 2) =
        ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) ^ 2
          + 2 * δ * ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ)
          + δ * ∑ T ∈ X.powerset, wt X δ T * 1 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
      rw [Finset.card_insert_of_notMem haT]
      push_cast
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [e0, h0]
    · rw [e1, h0, h1]
      push_cast
      ring
    · rw [e2, h0, h1, h2]
      push_cast
      ring
end Formalism.BehrendSets.Select
