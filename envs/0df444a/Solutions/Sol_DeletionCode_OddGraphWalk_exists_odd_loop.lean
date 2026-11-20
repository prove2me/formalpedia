-- Prove2me | solution 1 for DeletionCode.OddGraphWalk.exists_odd_loop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:06.388693+00:00
-- url     : https://prove2.me/submissions/38caab69-0b39-4b42-b1af-d2cf778b8a48

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OddGraphWalk

set_option autoImplicit true
open DeletionCode DeletionCode.OddGraphWalk
variable {V : Type*} {G : SimpleGraph V}
namespace DeletionCode.OddGraphWalk
theorem _root_.solution (hnot : ¬ G.Colorable 2) :
    ∃ u : V, ∃ q : G.Walk u u, Odd q.length := by
  classical
  by_contra hnone
  apply hnot
  apply SimpleGraph.two_colorable_iff_forall_loop_even.mpr
  intro u q
  exact Nat.not_odd_iff_even.mp (fun hq => hnone ⟨u, q, hq⟩)
end DeletionCode.OddGraphWalk
