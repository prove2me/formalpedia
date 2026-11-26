-- Prove2me | solution 1 for Erdos266.sixteen_le_bigN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:43:05.259821+00:00
-- url     : https://prove2.me/submissions/cfec8b6b-517e-45d3-b1e1-6c384f3ea7eb

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) : 16 ≤ bigN k := by
  calc (16:ℕ) = 2 ^ 4 := by norm_num
  _ ≤ 2 ^ (k ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  _ = bigN k := rfl
end Erdos266
