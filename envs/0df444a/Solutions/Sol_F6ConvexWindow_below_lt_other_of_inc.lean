-- Prove2me | solution 1 for F6ConvexWindow.below_lt_other_of_inc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:45:19.593431+00:00
-- url     : https://prove2.me/submissions/3e756cfb-7855-4663-9efd-98b542913ba7

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
theorem _root_.solution {T : Finset V} (ht : T.card = 3)
    {x s y : V} (hx : Below T x) (hs : s ∈ T) (hy : y ∈ T)
    (hsy : s ≠ y) (hxs : IncRel x s) : x < y := by
  classical
  by_contra hxy
  have hsub : T.filter (fun t => x < t) ⊆ (T.erase s).erase y := by
    intro t ht'
    obtain ⟨htT, hxt⟩ := mem_filter.mp ht'
    refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, htT⟩⟩
    · intro h; exact hxy (h ▸ hxt)
    · intro h; exact hxs.1 (h ▸ hxt.le)
  have hc := card_le_card hsub
  rw [card_erase_of_mem (mem_erase.mpr ⟨hsy.symm, hy⟩), card_erase_of_mem hs, ht] at hc
  unfold Below at hx
  omega
end F6ConvexWindow
