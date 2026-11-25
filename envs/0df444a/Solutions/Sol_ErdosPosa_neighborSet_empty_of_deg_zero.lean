-- Prove2me | solution 1 for ErdosPosa.neighborSet_empty_of_deg_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:28:48.050752+00:00
-- url     : https://prove2.me/submissions/2da01d49-3a9b-43e5-b6a8-5f0ea00400c9

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Definitions.Def_ErdosPosaLib_EPMaximal

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution [Finite V] {H : SimpleGraph V} {v : V} (h : deg H v = 0) :
    H.neighborSet v = ∅ :=
  (Set.ncard_eq_zero (Set.toFinite _)).1 h
end ErdosPosa
