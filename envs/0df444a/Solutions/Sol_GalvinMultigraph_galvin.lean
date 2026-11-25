-- Prove2me | solution 1 for GalvinMultigraph.galvin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:06.171323+00:00
-- url     : https://prove2.me/submissions/108b8b6b-144c-494c-a7c4-7440fb045154

module
public import Definitions.Def_GalvinMultigraph_Gadget
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinMultigraph_Main
public import Theorems.Thm_GalvinMultigraph_degreeA_le_maxDegree
public import Theorems.Thm_GalvinMultigraph_degreeB_le_maxDegree
public import Theorems.Thm_GalvinMultigraph_galvin_of_degree_bound

set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph
open Finset
variable {A B E Color : Type*}
namespace GalvinMultigraph
theorem _root_.solution [Fintype A] [Fintype B] [Finite E]
    (a : E → A) (b : E → B) (L : E → Finset Color)
    (hL : ∀ e, maxDegree a b ≤ (L e).card) :
    ∃ c : E → Color, (∀ e, c e ∈ L e) ∧ Proper a b c :=
  galvin_of_degree_bound a b (maxDegree a b)
    (degreeA_le_maxDegree a b) (degreeB_le_maxDegree a b) L hL
end GalvinMultigraph
