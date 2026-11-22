-- Prove2me | solution 1 for Bl.general_b_fact_right_rest.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:58.059149+00:00
-- url     : https://prove2.me/submissions/08739818-c4ee-494e-815c-f5d350250884

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightRest_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u_1 u_2
namespace Bl.general_b_fact_right_rest
private theorem aux {α : Type u_1} {β : Type u_2} (f : α → β) (t : Multiset α) :
    ∀ s : Multiset β, s ≤ t.map f → ∃ u : Multiset α, u ≤ t ∧ u.map f = s := by
  induction t using Multiset.induction_on with
  | empty =>
    intro s hs
    rw [Multiset.map_zero, Multiset.le_zero] at hs
    exact ⟨0, le_refl _, by rw [Multiset.map_zero, hs]⟩
  | cons a t ih =>
    intro s hs
    rw [Multiset.map_cons] at hs
    by_cases h : f a ∈ s
    · obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem h
      rw [Multiset.cons_le_cons_iff] at hs
      obtain ⟨u, hu, hmap⟩ := ih s' hs
      exact ⟨a ::ₘ u, (Multiset.cons_le_cons_iff a).mpr hu, by rw [Multiset.map_cons, hmap]⟩
    · obtain ⟨u, hu, hmap⟩ := ih s ((Multiset.le_cons_of_notMem h).mp hs)
      exact ⟨u, hu.trans (Multiset.le_cons_self t a), hmap⟩
end Bl.general_b_fact_right_rest
end

set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact_right_rest
namespace Bl.general_b_fact_right_rest
theorem _root_.solution :
  ∀ {α : Type u_1} {β : Type u_2} [DecidableEq.{u_2 + 1} β] (f : α → β) (t : Multiset.{u_1} α) (s : Multiset.{u_2} β),
  LE.le.{u_2} s (Multiset.map.{u_2, u_1} f t) →
    Exists.{u_1 + 1} fun (u : Multiset.{u_1} α) ↦ And (LE.le.{u_1} u t) (Eq.{u_2 + 1} (Multiset.map.{u_2, u_1} f u) s) := by
  intro α β _ f t s h
  exact aux f t s h
end Bl.general_b_fact_right_rest
