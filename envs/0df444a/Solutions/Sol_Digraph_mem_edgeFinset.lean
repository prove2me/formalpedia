-- Prove2me | solution 1 for Digraph.mem_edgeFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:44.393589+00:00
-- url     : https://prove2.me/submissions/68bfc398-ad30-480c-8a9b-ff980022484b

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
theorem _root_.solution [Fintype V] [DecidableEq V] {G : Digraph V}
    [DecidableRel G.Adj] {e : V × V} : e ∈ G.edgeFinset ↔ G.Adj e.1 e.2 := by
  simp [edgeFinset]
end Digraph
