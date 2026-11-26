-- Prove2me | solution 1 for Erdos266.one_le_bigN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:39:42.764421+00:00
-- url     : https://prove2.me/submissions/2b64d2c4-fb40-40b6-81ca-6f3face4d995

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (k : ℕ) : 1 ≤ bigN k := Nat.one_le_two_pow
end Erdos266
