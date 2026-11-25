-- Prove2me | solution 1 for ErdosPosa.deg_deleteEdge_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:33.413467+00:00
-- url     : https://prove2.me/submissions/90966c79-3012-45a1-9852-38b19bf3fc58

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Theorems.Thm_ErdosPosa_nbr_deleteEdge_left

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
    deg (H.deleteEdges {s(y, z)}) y = deg H y - 1 := by
  rw [deg, nbr_deleteEdge_left hyz,
    Set.ncard_sdiff_singleton_of_mem (show z ∈ H.neighborSet y from hyz)]; rfl
end ErdosPosa
