-- Prove2me | solution 1 for Erdos266.cross_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:45:38.740537+00:00
-- url     : https://prove2.me/submissions/85f2ea33-f1e7-4e77-89f4-14f4920693b0

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
public import Theorems.Thm_Erdos266_bigN_pos
public import Theorems.Thm_Erdos266_bigN_succ
public import Theorems.Thm_Erdos266_succ_le_two_pow
public import Theorems.Thm_Erdos266_two_mul_bigM_lt

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) :
    k * bigN k + bigM k + bigM (k + 1) < bigN (k + 1) := by
  have h1 : bigM k < bigN k := by
    have := two_mul_bigM_lt hk
    omega
  have h2 : 2 * bigM (k + 1) < bigN (k + 1) := two_mul_bigM_lt (by omega)
  have h3 : 2 * (k + 1) * bigN k ≤ bigN (k + 1) := by
    rw [bigN_succ]
    have h4 : 2 * (k + 1) ≤ 2 ^ (2 * k + 1) := by
      have h5 := succ_le_two_pow (2 * k)
      have : 2 * (k + 1) ≤ 2 * (2 * k + 1) := by omega
      calc 2 * (k + 1) ≤ 2 * (2 * k + 1) := this
      _ ≤ 2 * 2 ^ (2 * k) := by omega
      _ = 2 ^ (2 * k + 1) := by ring
    exact Nat.mul_le_mul_right _ h4
  nlinarith [bigN_pos k, bigN_pos (k + 1)]
end Erdos266
