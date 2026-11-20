-- Prove2me | solution 1 for DeletionCode.BipartiteSelection.componentColor_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:01.789481+00:00
-- url     : https://prove2.me/submissions/911f7da9-a57c-4782-9820-b1464358d212

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
theorem _root_.solution (C : G.ConnectedComponent) (hC : C.toSimpleGraph.Colorable 2)
    {v w : C} (hvw : C.toSimpleGraph.Adj v w) :
    componentColor G C v ≠ componentColor G C w := by
  classical
  simpa only [componentColor, dif_pos hC] using hC.some.valid hvw
end DeletionCode.BipartiteSelection
