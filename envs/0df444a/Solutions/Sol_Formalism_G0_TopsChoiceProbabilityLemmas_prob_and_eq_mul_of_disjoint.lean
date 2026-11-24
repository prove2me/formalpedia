-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.prob_and_eq_mul_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:40.828339+00:00
-- url     : https://prove2.me/submissions/b0efb0ae-9828-4e07-94b7-ad1bc584ff35

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_sum_powerset_union_disj
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_w_union

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
theorem _root_.solution (S R : Finset ℕ) (δ : ℝ) (h : Disjoint S R) (A B : Finset ℕ → Prop) :
    P (S ∪ R) δ (fun t => A (t ∩ S) ∧ B (t ∩ R)) = P S δ A * P R δ B := by
  classical
  unfold P
  beta_reduce
  rw [sum_powerset_union_disj S R h, sum_mul_sum]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  have ha' := mem_powerset.1 ha
  have hb' := mem_powerset.1 hb
  have e1 : (a ∪ b) ∩ S = a := by
    rw [union_inter_distrib_right, inter_eq_left.2 ha',
      disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left hb' h.symm), union_empty]
  have e2 : (a ∪ b) ∩ R = b := by
    rw [union_inter_distrib_right, inter_eq_left.2 hb',
      disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left ha' h), empty_union]
  rw [e1, e2, w_union δ h ha' hb']
  by_cases hA : A a <;> by_cases hB : B b <;> simp [hA, hB]
end Formalism.G0.TopsChoiceProbabilityLemmas
