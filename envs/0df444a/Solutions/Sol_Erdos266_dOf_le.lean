-- Prove2me | solution 1 for Erdos266.dOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:47:36.953786+00:00
-- url     : https://prove2.me/submissions/a53becc0-9f2a-4951-ba05-b025539d9265

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (k : ℕ) : dOf k ≤ k := Nat.findGreatest_le k
end Erdos266
