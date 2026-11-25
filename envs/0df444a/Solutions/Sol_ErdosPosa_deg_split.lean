-- Prove2me | solution 1 for ErdosPosa.deg_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:23.432345+00:00
-- url     : https://prove2.me/submissions/c32c2191-94b4-4128-9a0c-5cc3fe56c87c

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable {H₀ : SimpleGraph V} {T : Set V}
namespace ErdosPosa
theorem _root_.solution [Finite V] (v : V) :
    deg H₀ v = (H₀.neighborSet v ∩ T).ncard + (H₀.neighborSet v \ T).ncard :=
  (Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)).symm
end ErdosPosa
