-- Prove2me | solution 1 for Digraph.deleteEdges_empty_depth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:58.511107+00:00
-- url     : https://prove2.me/submissions/e53b004e-05a1-4ab9-9dae-cbf156257e84

module
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs

set_option autoImplicit true
@[expose] public section
public section
open Digraph
variable {V : Type*}
namespace Digraph
theorem _root_.solution (G : Digraph V) :
    (G.deleteEdges ∅).depth = G.depth := by
  unfold Digraph.depth
  congr 1
  ext m
  exact ⟨fun ⟨p, hp⟩ => ⟨p, fun i h => (hp i h).1⟩,
    fun ⟨p, hp⟩ => ⟨p, fun i h => ⟨hp i h, Finset.notMem_empty _⟩⟩⟩
end Digraph
