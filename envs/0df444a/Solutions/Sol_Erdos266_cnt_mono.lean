-- Prove2me | solution 1 for Erdos266.cnt_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:58:26.63585+00:00
-- url     : https://prove2.me/submissions/198e421b-d76e-486d-88c9-eac511c4f523

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
theorem _root_.solution : Monotone cnt := by
  apply monotone_nat_of_le_succ
  intro k
  rw [cnt_succ]
  omega
end Erdos266
