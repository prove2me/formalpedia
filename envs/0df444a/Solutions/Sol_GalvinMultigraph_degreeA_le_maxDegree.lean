-- Prove2me | solution 1 for GalvinMultigraph.degreeA_le_maxDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:49:53.711804+00:00
-- url     : https://prove2.me/submissions/0f38360e-4ab1-480d-8070-c4797499d570

module
public import Definitions.Def_GalvinMultigraph_Gadget
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinMultigraph_Main
public import Theorems.Thm_LeanPool_Vizing_PEC_Extends_trans


set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph
open Finset
variable {A B E Color : Type*}
namespace GalvinMultigraph
theorem _root_.solution [Fintype A] [Fintype B] (a : E → A) (b : E → B) (x : A) :
    Nat.card {e // a e = x} ≤ maxDegree a b :=
  (Finset.le_sup (f := fun x => Nat.card {e // a e = x}) (mem_univ x)).trans
    (le_max_left _ _)
end GalvinMultigraph
