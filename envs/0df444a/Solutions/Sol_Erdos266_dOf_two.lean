-- Prove2me | solution 1 for Erdos266.dOf_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:03:07.80342+00:00
-- url     : https://prove2.me/submissions/f7daa3af-a1d5-4338-9c69-c02b9332baf8

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
public import Theorems.Thm_Erdos266_add_two_le_mseq
public import Theorems.Thm_Erdos266_dOf_lt_iff


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution : dOf 2 = 0 := by
  have h1 : dOf 2 < 1 := by
    rw [dOf_lt_iff le_rfl]
    have := add_two_le_mseq 1
    omega
  omega
end Erdos266
