-- Prove2me | solution 1 for Erdos266.bigN_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:40:09.674484+00:00
-- url     : https://prove2.me/submissions/6c0c8ca8-acd6-4eb2-b759-9b1d7452d9d6

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (k : ℕ) : bigN (k + 1) = 2 ^ (2 * k + 1) * bigN k := by
  rw [bigN, bigN, ← pow_add]
  congr 1
  ring
end Erdos266
