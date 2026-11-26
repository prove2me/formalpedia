-- Prove2me | solution 1 for Erdos266.bigN_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:43:40.843818+00:00
-- url     : https://prove2.me/submissions/17affe11-0ca6-443b-b213-0bed17677289

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution : StrictMono bigN := by
  intro a b hab
  apply Nat.pow_lt_pow_right (by norm_num)
  exact Nat.pow_lt_pow_left hab (by norm_num)
end Erdos266
