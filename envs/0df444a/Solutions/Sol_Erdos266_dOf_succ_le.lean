-- Prove2me | solution 1 for Erdos266.dOf_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:52:26.144562+00:00
-- url     : https://prove2.me/submissions/95bad079-e2d7-4186-bccc-2344cfac5d8b

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_mseq_lt_succ
public import Theorems.Thm_Erdos266_mseq_strictMono
public import Theorems.Thm_Erdos266_two_le_mseq
public import Theorems.Thm_Erdos266_mseq_dOf_le
public import Theorems.Thm_Erdos266_le_dOf

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (k : ℕ) : dOf (k + 1) ≤ dOf k + 1 := by
  rcases Nat.lt_or_ge (k + 1) 2 with h | h
  · have hk0 : k = 0 := by omega
    subst hk0
    have h1 : dOf 1 = 0 := by
      rw [dOf, Nat.findGreatest_eq_zero_iff]
      intro d hd _
      have := two_le_mseq d
      omega
    change dOf 1 ≤ dOf 0 + 1
    omega
  · by_contra hcon
    push Not at hcon
    have h1 : mseq (dOf k + 2) ≤ k + 1 := by
      have := mseq_strictMono.monotone (show dOf k + 2 ≤ dOf (k + 1) by omega)
      have h2 := mseq_dOf_le h
      omega
    have h2 : mseq (dOf k + 1) < mseq (dOf k + 2) := mseq_lt_succ _
    have h3 : mseq (dOf k + 1) ≤ k := by omega
    have := le_dOf h3
    omega
end Erdos266
