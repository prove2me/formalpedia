-- Prove2me | solution 1 for ErdosPosa.dsum_deleteEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:32:14.555302+00:00
-- url     : https://prove2.me/submissions/b305d7d6-5ddd-4a1b-9ccc-07f7176f0f7c

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Theorems.Thm_ErdosPosa_deg_mono
public import Theorems.Thm_ErdosPosa_deg_deleteEdge_left
public import Theorems.Thm_ErdosPosa_deg_pos_of_adj


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {H : SimpleGraph V} {y z : V}
variable [Fintype V]
namespace ErdosPosa
theorem _root_.solution (hyz : H.Adj y z) : dsum (H.deleteEdges {s(y, z)}) < dsum H := by
  unfold dsum
  apply Finset.sum_lt_sum
  · intro v _; exact deg_mono (deleteEdges_le _) v
  · refine ⟨y, Finset.mem_univ _, ?_⟩
    rw [deg_deleteEdge_left hyz]
    have := deg_pos_of_adj hyz
    omega
end ErdosPosa
