-- Prove2me | solution 1 for F6ConvexWindow.above_not_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:33:44.980868+00:00
-- url     : https://prove2.me/submissions/e5b2309d-31db-49e7-8bf2-548bc0fe669b

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution {T : Finset V} (ht : Antichain T) {x t : V}
    (hx : Above T x) (htT : t ∈ T) : ¬ x ≤ t := by
  classical
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (T.filter (fun a => a < x)).card by
    unfold Above at hx
    omega)
  obtain ⟨ha, hax⟩ := mem_filter.mp ha
  intro hxt
  have hat := ht a ha t htT (hax.le.trans hxt)
  exact hax.not_ge (hat.symm ▸ hxt)
end F6ConvexWindow
