-- Prove2me | solution 1 for F6ConvexWindow.pairCount_union_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:54:13.304412+00:00
-- url     : https://prove2.me/submissions/290b754b-ebf6-40c1-8099-d9e274aaf3e1

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_inducedPairs_union_subset

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (U W : Finset V) :
    pairCount (U ∪ W) ≤ pairCount U + pairCount W + (crossPairs (U \ W) (W \ U)).card := by
  have h := (card_le_card (inducedPairs_union_subset U W)).trans (card_union_le _ _)
  have h' := card_union_le (inducedPairs U) (inducedPairs W)
  unfold pairCount
  omega
end F6ConvexWindow
