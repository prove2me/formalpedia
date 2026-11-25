-- Prove2me | solution 1 for ErdosPosa.deg_deleteEdge_other
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:26:44.185593+00:00
-- url     : https://prove2.me/submissions/130d861c-ca9a-41cd-8b6c-51a4c3f00ca1

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
theorem _root_.solution (v : V) (hvy : v ≠ y) (hvz : v ≠ z) :
    deg (H.deleteEdges {s(y, z)}) v = deg H v := by
  unfold deg
  congr 1
  ext w
  simp only [mem_neighborSet, deleteEdges_adj, Set.mem_singleton_iff, and_iff_left_iff_imp]
  intro _ he
  rw [Sym2.eq_iff] at he
  rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hvy h1
  · exact hvz h1
end ErdosPosa
