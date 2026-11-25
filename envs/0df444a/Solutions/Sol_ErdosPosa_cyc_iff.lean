-- Prove2me | solution 1 for ErdosPosa.cyc_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:20:47.745954+00:00
-- url     : https://prove2.me/submissions/34487bde-4af7-4ff6-b4cb-8cd55f00f37f

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {H : SimpleGraph V} {S : Set V} :
    Cyc H S ↔ ∃ u v, (restr H S).Adj u v ∧ ((restr H S).deleteEdges {s(u, v)}).Reachable u v := by
  unfold Cyc
  rw [isAcyclic_iff_forall_adj_isBridge]
  simp only [isBridge_iff, not_forall, not_not]
  constructor
  · rintro ⟨u, v, h1, h2⟩; exact ⟨u, v, h1, h2⟩
  · rintro ⟨u, v, h1, h2⟩; exact ⟨u, v, h1, h2⟩
end ErdosPosa
