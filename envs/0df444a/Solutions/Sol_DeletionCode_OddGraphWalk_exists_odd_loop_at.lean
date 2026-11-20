-- Prove2me | solution 1 for DeletionCode.OddGraphWalk.exists_odd_loop_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:47.770463+00:00
-- url     : https://prove2.me/submissions/94ed1d66-be75-43f8-82a4-718d6e0d6fed

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OddGraphWalk
import Theorems.Thm_DeletionCode_OddGraphWalk_exists_odd_loop

set_option autoImplicit true
open DeletionCode DeletionCode.OddGraphWalk
variable {V : Type*} {G : SimpleGraph V}
namespace DeletionCode.OddGraphWalk
theorem _root_.solution (hconnected : G.Connected)
    (hnot : ¬ G.Colorable 2) (x : V) :
    ∃ q : G.Walk x x, Odd q.length := by
  classical
  obtain ⟨u, q, hq⟩ := exists_odd_loop hnot
  let a : G.Walk x u := (hconnected x u).some
  refine ⟨(a.append q).append a.reverse, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  obtain ⟨r, hr⟩ := hq
  refine ⟨a.length + r, ?_⟩
  omega
end DeletionCode.OddGraphWalk
