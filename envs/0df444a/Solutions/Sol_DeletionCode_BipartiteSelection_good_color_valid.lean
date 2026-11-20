-- Prove2me | solution 1 for DeletionCode.BipartiteSelection.good_color_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:03.400736+00:00
-- url     : https://prove2.me/submissions/8023983a-9572-4939-9f25-f36d02721d1e

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_BipartiteSelection
import Theorems.Thm_DeletionCode_BipartiteSelection_componentColor_valid
import Theorems.Thm_DeletionCode_BipartiteSelection_color_eq_component

set_option autoImplicit true
open DeletionCode DeletionCode.BipartiteSelection
open SimpleGraph
open scoped BigOperators
variable {V : Type*} (G : SimpleGraph V)
namespace DeletionCode.BipartiteSelection
theorem _root_.solution {v w : V} (hv : Good G v) (hvw : G.Adj v w) :
    color G v ≠ color G w := by
  let C := G.connectedComponentMk v
  have hvC : v ∈ C := rfl
  have hwC : w ∈ C :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hvw).symm
  rw [color_eq_component G C v hvC, color_eq_component G C w hwC]
  exact componentColor_valid G C hv (show C.toSimpleGraph.Adj ⟨v, hvC⟩ ⟨w, hwC⟩ from hvw)
end DeletionCode.BipartiteSelection
