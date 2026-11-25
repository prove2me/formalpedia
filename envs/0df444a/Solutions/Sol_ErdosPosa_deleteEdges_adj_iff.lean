-- Prove2me | solution 1 for ErdosPosa.deleteEdges_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:20:49.516061+00:00
-- url     : https://prove2.me/submissions/07ffff8f-efef-4bf2-b244-1345102be74d

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
theorem _root_.solution {G : SimpleGraph V} {u v a b : V} :
    (G.deleteEdges {s(u, v)}).Adj a b ↔ G.Adj a b ∧ s(a, b) ≠ s(u, v) := by
  simp [deleteEdges_adj]
end ErdosPosa
