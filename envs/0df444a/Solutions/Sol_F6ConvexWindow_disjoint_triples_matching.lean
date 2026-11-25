-- Prove2me | solution 1 for F6ConvexWindow.disjoint_triples_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:52:20.170811+00:00
-- url     : https://prove2.me/submissions/fbc6516a-251e-49ec-98d4-ed0ab1bd36cf

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_triple_incomparables_le_one


set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T) (hd : Disjoint S T) :
    (∀ x ∈ S, (T.filter (IncRel x)).card ≤ 1) ∧
    (∀ y ∈ T, (S.filter (IncRel y)).card ≤ 1) := by
  constructor
  · intro x hx
    exact triple_incomparables_le_one hw hci ht.1 ht.2
      (fun h => disjoint_left.mp hd hx h)
  · intro y hy
    exact triple_incomparables_le_one hw hci hs.1 hs.2
      (fun h => disjoint_left.mp hd h hy)
end F6ConvexWindow
