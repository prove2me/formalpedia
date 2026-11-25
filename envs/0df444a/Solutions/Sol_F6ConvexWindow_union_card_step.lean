-- Prove2me | solution 1 for F6ConvexWindow.union_card_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:03:22.487895+00:00
-- url     : https://prove2.me/submissions/76937404-d12d-44d3-9963-0a9b65098720

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution {U T : Finset V} (ht : T.card = 3) (hi : (U ∩ T).card ≤ 1) :
    (U ∪ T).card = U.card + 2 + if Disjoint U T then 1 else 0 := by
  have hc := card_union_add_card_inter U T
  by_cases hd : Disjoint U T
  · rw [if_pos hd]
    rw [disjoint_iff_inter_eq_empty.mp hd, card_empty, ht] at hc
    omega
  · rw [if_neg hd]
    have hp : 0 < (U ∩ T).card := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hd (disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hz))
    omega
end F6ConvexWindow
