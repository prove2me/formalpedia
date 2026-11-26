-- Prove2me | solution 1 for Erdos266.bigM_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:42:11.694393+00:00
-- url     : https://prove2.me/submissions/3e39a9d3-ef2f-4974-a640-3e58cb9326cc

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (k : ℕ) : bigM k ≤ Nat.sqrt (bigN k) := min_le_right _ _
end Erdos266
