-- Prove2me | solution 1 for Erdos266.succ_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:39:29.484006+00:00
-- url     : https://prove2.me/submissions/18d5f769-a257-43b7-ab95-df58c1342fbc

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (k : ℕ) : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
end Erdos266
