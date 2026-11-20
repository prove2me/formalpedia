-- Prove2me | solution 1 for DeletionCode.BipartiteSelection.good_graph_colorable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:00.291559+00:00
-- url     : https://prove2.me/submissions/bc564b63-39ab-4ae0-9626-690d80173a27

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_BipartiteSelection
import Theorems.Thm_DeletionCode_BipartiteSelection_good_color_valid

set_option autoImplicit true
open DeletionCode DeletionCode.BipartiteSelection
open SimpleGraph
open scoped BigOperators
variable {V : Type*} (G : SimpleGraph V)
namespace DeletionCode.BipartiteSelection
theorem _root_.solution : (G.induce {v | Good G v}).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => color G v.val) ?_⟩
  intro v w hvw
  exact good_color_valid G v.property hvw
end DeletionCode.BipartiteSelection
