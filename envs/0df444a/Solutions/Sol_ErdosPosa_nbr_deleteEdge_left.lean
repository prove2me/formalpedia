-- Prove2me | solution 1 for ErdosPosa.nbr_deleteEdge_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:29:02.953349+00:00
-- url     : https://prove2.me/submissions/26d3fa2c-27fa-409e-ae87-0386d0b49e06

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



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
    (H.deleteEdges {s(y, z)}).neighborSet y = H.neighborSet y \ {z} := by
  ext w
  simp only [mem_neighborSet, deleteEdges_adj, Set.mem_singleton_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨h, hne⟩; exact ⟨h, fun h' => hne (h' ▸ rfl)⟩
  · rintro ⟨h, hne⟩
    refine ⟨h, fun he => hne ?_⟩
    rw [Sym2.eq_iff] at he
    rcases he with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hyz.ne
end ErdosPosa
