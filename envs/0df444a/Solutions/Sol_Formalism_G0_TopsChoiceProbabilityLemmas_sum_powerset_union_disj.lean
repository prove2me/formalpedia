-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.sum_powerset_union_disj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:20.514475+00:00
-- url     : https://prove2.me/submissions/d57a50c1-a007-4a03-9fba-7d66c5cc8837

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined

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
theorem _root_.solution {β : Type*} [AddCommMonoid β] (S R : Finset ℕ)
    (h : Disjoint S R) (F : Finset ℕ → β) :
    ∑ t ∈ (S ∪ R).powerset, F t = ∑ a ∈ S.powerset, ∑ b ∈ R.powerset, F (a ∪ b) := by
  induction R using Finset.induction_on generalizing F with
  | empty => simp
  | insert x R hx ih =>
    have hxS : x ∉ S := fun hs => disjoint_left.1 h hs (mem_insert_self x R)
    have h' : Disjoint S R := disjoint_of_subset_right (subset_insert x R) h
    rw [union_insert, sum_powerset_insert (by simp [hx, hxS])]
    rw [ih h', ih h' (fun t => F (insert x t))]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    rw [sum_powerset_insert hx]
    congr 1
    apply sum_congr rfl
    intro b _
    rw [union_insert]
end Formalism.G0.TopsChoiceProbabilityLemmas
