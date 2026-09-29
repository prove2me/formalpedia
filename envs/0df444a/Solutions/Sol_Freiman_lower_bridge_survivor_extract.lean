-- Prove2me | solution 1 for Freiman.lower_bridge_survivor_extract
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:52:08.444221+00:00
-- url     : https://prove2.me/submissions/2514c854-8642-43b5-87d8-10ce6bbaf9b9

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib
open Freiman
set_option maxHeartbeats 1000000

theorem solution (c : LowerBridgeCase) (n k : ℕ)
    (hc : lowerBridgeZero c = decide (n=0)) (h : lowerBridgeFacts c n k) : lowerBridgeSurvivorLarge c n k := by
  let s := lowerBridgeAppend (lowerBridgePair c n k) ([1],[1])
  have hw : lowerWidth s.2 < lowerWidth s.1 := by
    cases c <;> exact h _ (List.mem_cons_self ..)
  have hh : lowerThreshold s (31/100) 3 63 25 66 ≤ lowerScale (lowerNormalize s) := by
    cases c <;> exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have ha : ¬ lowerA s 9 := by
    cases c <;> exact h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hn : lowerNormalize s = s := by
    unfold lowerNormalize
    simp [le_of_lt hw]
  exact ⟨hn, by simpa only [hn] using hh, ha⟩

#print axioms solution
