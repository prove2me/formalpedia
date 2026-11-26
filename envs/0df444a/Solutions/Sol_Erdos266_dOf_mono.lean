-- Prove2me | solution 1 for Erdos266.dOf_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:52:25.494459+00:00
-- url     : https://prove2.me/submissions/d51c069b-cb84-408f-9616-ff8b3648bc25

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_two_le_mseq
public import Theorems.Thm_Erdos266_mseq_dOf_le
public import Theorems.Thm_Erdos266_le_dOf

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution : Monotone dOf := by
  intro a b hab
  rcases Nat.lt_or_ge a 2 with h | h
  · have : dOf a = 0 := by
      rw [dOf, Nat.findGreatest_eq_zero_iff]
      intro d hd hdle
      have := two_le_mseq d
      omega
    omega
  · exact le_dOf (le_trans (mseq_dOf_le h) hab)
end Erdos266
