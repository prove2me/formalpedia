-- Prove2me | solution 1 for Erdos266.bigM_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:42:03.346255+00:00
-- url     : https://prove2.me/submissions/be8d5176-8e20-4b85-8b57-34713800c125

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (k : ℕ) : bigM k * bigM k ≤ bigN k := by
  have h := Nat.sqrt_le' (bigN k)
  rw [pow_two] at h
  exact le_trans (Nat.mul_le_mul (min_le_right _ _) (min_le_right _ _)) h
end Erdos266
