-- Prove2me | solution 1 for ErdosPosa.deg_deleteEdge_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:32:11.583877+00:00
-- url     : https://prove2.me/submissions/8b8b817f-b16e-4e93-9cfd-40197281998f

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Theorems.Thm_ErdosPosa_deg_deleteEdge_left

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {H : SimpleGraph V} {y z : V}
omit [Finite V]
namespace ErdosPosa
theorem _root_.solution (hyz : H.Adj y z) :
    deg (H.deleteEdges {s(y, z)}) z = deg H z - 1 := by
  have : s(y, z) = s(z, y) := Sym2.eq_swap
  rw [this]; exact deg_deleteEdge_left hyz.symm
end ErdosPosa
