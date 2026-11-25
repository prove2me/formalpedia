-- Prove2me | solution 1 for GalvinMultigraph.maxDegree_le_of_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:58:41.628546+00:00
-- url     : https://prove2.me/submissions/2fec7689-15f0-41e4-8682-e5ee37216f59

module
public import Definitions.Def_GalvinMultigraph_Gadget
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinMultigraph_Main
public import Theorems.Thm_GalvinMultigraph_degree_bounds_of_proper

set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph
open Finset
variable {A B E Color : Type*}
namespace GalvinMultigraph
theorem _root_.solution [Fintype A] [Fintype B] [Finite E] [Fintype Color]
    (a : E → A) (b : E → B) (c : E → Color) (hc : Proper a b c) :
    maxDegree a b ≤ Fintype.card Color := by
  have h := degree_bounds_of_proper a b c hc
  exact max_le (Finset.sup_le fun x _ => h.1 x) (Finset.sup_le fun y _ => h.2 y)
end GalvinMultigraph
