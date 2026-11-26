-- Prove2me | solution 1 for Erdos266.kOf_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:57:18.739661+00:00
-- url     : https://prove2.me/submissions/ec6ed581-f1df-4dbc-bc3b-1588b3c8ab8d

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
theorem _root_.solution (n : ℕ) : n < cnt (kOf n + 1) := Nat.find_spec (cnt_unbounded n)
end Erdos266
