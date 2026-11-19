-- Prove2me | solution 1 for DeletionCode.BipartiteSelection.mem_goodVertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:48:45.468893+00:00
-- url     : https://prove2.me/submissions/7a270f62-8737-438f-a24f-a39186aa2d43

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_BipartiteSelection

set_option autoImplicit true
open DeletionCode DeletionCode.BipartiteSelection
open SimpleGraph
open scoped BigOperators
variable {V : Type*} (G : SimpleGraph V)
variable [Fintype V]
namespace DeletionCode.BipartiteSelection
theorem _root_.solution (v : V) : v ∈ goodVertices G ↔ Good G v := by
  classical
  simp only [goodVertices, Finset.mem_filter, Finset.mem_univ, true_and]
end DeletionCode.BipartiteSelection
