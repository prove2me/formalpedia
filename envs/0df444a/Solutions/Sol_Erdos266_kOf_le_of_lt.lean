-- Prove2me | solution 1 for Erdos266.kOf_le_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:00:31.335677+00:00
-- url     : https://prove2.me/submissions/be720308-bee2-4308-912a-964213d6a6d6

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
theorem _root_.solution {n k : ℕ} (h : n < cnt (k + 1)) : kOf n ≤ k :=
  Nat.find_min' (cnt_unbounded n) h
end Erdos266
