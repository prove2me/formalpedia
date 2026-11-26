-- Prove2me | solution 1 for Erdos266.run_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:03:17.205091+00:00
-- url     : https://prove2.me/submissions/a52f7fbd-3894-4330-8589-b25f0d05eeee

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution : run 1 = initSt := by
  rw [run, if_pos (by norm_num)]
end Erdos266
