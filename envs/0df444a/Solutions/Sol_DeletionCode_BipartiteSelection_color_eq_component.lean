-- Prove2me | solution 1 for DeletionCode.BipartiteSelection.color_eq_component
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:10.44201+00:00
-- url     : https://prove2.me/submissions/bc8d68cb-772f-487d-a685-727b7170e197

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
namespace DeletionCode.BipartiteSelection
theorem _root_.solution (C : G.ConnectedComponent) (v : V) (hv : v ∈ C) :
    color G v = componentColor G C ⟨v, hv⟩ := by
  change G.connectedComponentMk v = C at hv
  subst C
  rfl
end DeletionCode.BipartiteSelection
