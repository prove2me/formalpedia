-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.prob_forall_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:46:21.535897+00:00
-- url     : https://prove2.me/submissions/2bb51ee0-49e2-479b-9dc5-507d11dbb767

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_true
import Theorems.Thm_P2M_Formalism_G0_TopsChoiceProbabilityLemmas_prob_and_eq_mul_of_disjoint__d38c33bc61b6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsChoiceProbabilityLemmas
theorem _root_.solution {ι : Type*} [DecidableEq ι] {U : Finset ℕ} (δ : ℝ) (F : Finset ι)
    (S : ι → Finset ℕ) (hS : ∀ i ∈ F, S i ⊆ U)
    (hd : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (E : ι → Finset ℕ → Prop) (hE : ∀ i ∈ F, Dep (S i) (E i)) :
    P U δ (fun t => ∀ i ∈ F, E i t) = ∏ i ∈ F, P U δ (E i) := by
  induction F using Finset.induction_on with
  | empty => simpa using prob_true U δ
  | insert k F hk ih =>
    rw [prod_insert hk]
    have hS' : ∀ i ∈ F, S i ⊆ U := fun i hi => hS i (mem_insert_of_mem hi)
    have hd' : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j) :=
      fun i hi j hj hij => hd i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij
    have hE' : ∀ i ∈ F, Dep (S i) (E i) := fun i hi => hE i (mem_insert_of_mem hi)
    rw [← ih hS' hd' hE']
    have hD : Dep (F.biUnion S) (fun t => ∀ i ∈ F, E i t) := by
      intro t
      apply forall₂_congr
      intro i hi
      rw [hE' i hi t, hE' i hi (t ∩ F.biUnion S), inter_assoc,
        inter_eq_right.2 (subset_biUnion_of_mem S hi)]
    have hdisj : Disjoint (S k) (F.biUnion S) := by
      rw [disjoint_biUnion_right]
      intro i hi
      exact hd k (mem_insert_self k F) i (mem_insert_of_mem hi) (fun h => hk (h ▸ hi))
    rw [← prob_and_eq_mul_of_disjoint₂ δ (hS k (mem_insert_self k F)) (biUnion_subset.2 hS') hdisj
      (hE k (mem_insert_self k F)) hD]
    congr 1
    funext t
    exact propext (forall_mem_insert _ _ _)
end Formalism.G0.TopsChoiceProbabilityLemmas
