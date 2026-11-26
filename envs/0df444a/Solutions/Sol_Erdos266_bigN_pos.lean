-- Prove2me | solution 1 for Erdos266.bigN_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:41:40.580563+00:00
-- url     : https://prove2.me/submissions/e707f8a4-b434-4547-9b59-8fd6af49ea26

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
public import Theorems.Thm_Erdos266_one_le_bigN

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (k : ℕ) : 0 < bigN k := one_le_bigN k
end Erdos266
