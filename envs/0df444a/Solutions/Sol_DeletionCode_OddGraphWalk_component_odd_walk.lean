-- Prove2me | solution 1 for DeletionCode.OddGraphWalk.component_odd_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:45.852172+00:00
-- url     : https://prove2.me/submissions/68d1ee4a-8cb1-4dfb-a37d-66405304a3e4

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OddGraphWalk
import Theorems.Thm_DeletionCode_OddGraphWalk_component_exists_odd_loop_at
import Theorems.Thm_DeletionCode_OddGraphWalk_indexed_of_odd_loop

set_option autoImplicit true
open DeletionCode DeletionCode.OddGraphWalk
variable {V : Type*} {G : SimpleGraph V}
namespace DeletionCode.OddGraphWalk
theorem _root_.solution (x : V)
    (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ m : ℕ, Odd m ∧ ∃ vertices : Fin (m + 1) → V,
      vertices 0 = x ∧ vertices (Fin.last m) = x ∧
        ∀ i : Fin m, G.Adj (vertices i.castSucc) (vertices i.succ) := by
  obtain ⟨q, hq⟩ := component_exists_odd_loop_at x hnot
  exact indexed_of_odd_loop q hq
end DeletionCode.OddGraphWalk
