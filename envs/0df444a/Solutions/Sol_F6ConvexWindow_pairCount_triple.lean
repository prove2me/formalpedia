-- Prove2me | solution 1 for F6ConvexWindow.pairCount_triple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:13:57.748404+00:00
-- url     : https://prove2.me/submissions/d4a67f6f-a9a8-489a-911a-59aadb70d93f

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
theorem _root_.solution {T : Finset V} (ht : IsTriple T) : pairCount T = 3 := by
  have he : inducedPairs T = T.powersetCard 2 := by
    apply filter_eq_self.mpr
    intro P hP
    have hsub := (mem_powersetCard.mp hP).1
    exact fun x hx y hy hxy => ht.1 x (hsub hx) y (hsub hy) hxy
  rw [pairCount, he, card_powersetCard, ht.2]
  decide
end F6ConvexWindow
