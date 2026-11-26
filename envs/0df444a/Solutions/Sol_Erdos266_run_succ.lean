-- Prove2me | solution 1 for Erdos266.run_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:55:33.23123+00:00
-- url     : https://prove2.me/submissions/e353d484-9952-4ea3-a023-f8e33ee8e374

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) : run (k + 1) = stepSt k (run k) := by
  rw [run, if_neg (by omega)]
end Erdos266
