-- Prove2me | solution 1 for DeletionCode.OddGraphWalk.connected_odd_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:57.793734+00:00
-- url     : https://prove2.me/submissions/8fa9352e-b626-4eac-932d-71824fe46ce5

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OddGraphWalk
import Theorems.Thm_DeletionCode_OddGraphWalk_exists_odd_loop_at
import Theorems.Thm_DeletionCode_OddGraphWalk_indexed_of_odd_loop

set_option autoImplicit true
open DeletionCode DeletionCode.OddGraphWalk
variable {V : Type*} {G : SimpleGraph V}
namespace DeletionCode.OddGraphWalk
theorem _root_.solution (hconnected : G.Connected)
    (hnot : ¬ G.Colorable 2) (x : V) :
    ∃ m : ℕ, Odd m ∧ ∃ vertices : Fin (m + 1) → V,
      vertices 0 = x ∧ vertices (Fin.last m) = x ∧
        ∀ i : Fin m, G.Adj (vertices i.castSucc) (vertices i.succ) := by
  obtain ⟨q, hq⟩ := exists_odd_loop_at hconnected hnot x
  exact indexed_of_odd_loop q hq
end DeletionCode.OddGraphWalk
