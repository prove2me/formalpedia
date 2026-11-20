-- Prove2me | solution 1 for DeletionCode.OddGraphWalk.component_exists_odd_loop_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:45.514259+00:00
-- url     : https://prove2.me/submissions/47d54259-596c-41bb-b265-49a5ac154f6e

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OddGraphWalk
import Theorems.Thm_DeletionCode_OddGraphWalk_exists_odd_loop_at

set_option autoImplicit true
open DeletionCode DeletionCode.OddGraphWalk
variable {V : Type*} {G : SimpleGraph V}
namespace DeletionCode.OddGraphWalk
theorem _root_.solution (x : V)
    (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ q : G.Walk x x, Odd q.length := by
  classical
  let C := G.connectedComponentMk x
  let xc : C := ⟨x, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  obtain ⟨q, hq⟩ := exists_odd_loop_at C.connected_toSimpleGraph hnot xc
  have hm : Odd (q.map C.toSimpleGraph_hom).length := by
    simpa only [SimpleGraph.Walk.length_map] using hq
  exact ⟨q.map C.toSimpleGraph_hom, hm⟩
end DeletionCode.OddGraphWalk
