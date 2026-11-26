-- Prove2me | solution 1 for Erdos266.four_mul_bigM_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:44:02.526316+00:00
-- url     : https://prove2.me/submissions/c29a3aba-b838-40c1-bb42-d899bb5557fb

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (k : ℕ) : 4 * k * bigM k ≤ bigN k := by
  calc 4 * k * bigM k ≤ 4 * k * (bigN k / (4 * k)) := by
        exact Nat.mul_le_mul_left _ (min_le_left _ _)
  _ ≤ bigN k := Nat.mul_div_le _ _
end Erdos266
