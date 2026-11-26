-- Prove2me | solution 1 for Erdos266.dOf_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:56:21.090322+00:00
-- url     : https://prove2.me/submissions/1f5cd32b-0c47-4c25-813d-a4c0ff6b87c2

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
public import Theorems.Thm_Erdos266_two_le_mseq


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} (hk : k < 2) : dOf k = 0 := by
  rw [dOf, Nat.findGreatest_eq_zero_iff]
  intro d hd _
  have := two_le_mseq d
  omega
end Erdos266
