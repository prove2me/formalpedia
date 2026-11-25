-- Prove2me | solution 1 for ErdosPosa.deg_pos_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:24:02.000176+00:00
-- url     : https://prove2.me/submissions/ec8fc5b7-62b6-433d-9055-638d3351b54d

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMoore
public import Definitions.Def_ErdosPosaLib_EPShort

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution [Finite V] {H : SimpleGraph V} {u w : V} (h : H.Adj u w) : 0 < deg H u :=
  Set.ncard_pos (Set.toFinite _) |>.2 ⟨w, h⟩
end ErdosPosa
