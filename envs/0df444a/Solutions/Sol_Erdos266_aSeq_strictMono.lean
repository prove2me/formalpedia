-- Prove2me | solution 1 for Erdos266.aSeq_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:13:25.726535+00:00
-- url     : https://prove2.me/submissions/350935a5-f696-48ac-9a5a-f28d932610b4

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_cnt_mono
public import Theorems.Thm_Erdos266_kOf_spec
public import Theorems.Thm_Erdos266_cnt_kOf_le
public import Theorems.Thm_Erdos266_jOf_lt
public import Theorems.Thm_Erdos266_kOf_le_of_lt
public import Theorems.Thm_Erdos266_le_kOf_of_cnt_le
public import Theorems.Thm_Erdos266_aSeq_cast
public import Theorems.Thm_Erdos266_elemZ_lt_within
public import Theorems.Thm_Erdos266_elemZ_cross

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution : StrictMono aSeq := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hZ : elemZ (kOf n) (n - cnt (kOf n)) < elemZ (kOf (n + 1)) (n + 1 - cnt (kOf (n + 1))) := by
    rcases Nat.lt_or_ge (n + 1) (cnt (kOf n + 1)) with hsame | hbound
    · -- same block, next slot
      have hk : kOf (n + 1) = kOf n := by
        have h1 : kOf (n + 1) ≤ kOf n := kOf_le_of_lt hsame
        have h2 : kOf n ≤ kOf (n + 1) := le_kOf_of_cnt_le (le_trans (cnt_kOf_le n) (by omega))
        omega
      have hj : n + 1 - cnt (kOf n) = (n - cnt (kOf n)) + 1 := by
        have := cnt_kOf_le n
        omega
      rw [hk, hj]
      apply elemZ_lt_within
      have h3 := jOf_lt (n + 1)
      rw [hk, hj] at h3
      exact h3
    · -- block boundary
      have hk : kOf n < kOf (n + 1) := by
        by_contra hc
        push Not at hc
        have h1 : cnt (kOf (n + 1) + 1) ≤ cnt (kOf n + 1) := cnt_mono (by omega)
        have h2 := kOf_spec (n + 1)
        omega
      exact elemZ_cross hk (jOf_lt n) (jOf_lt (n + 1))
  have h1 := aSeq_cast n
  have h2 := aSeq_cast (n + 1)
  omega
end Erdos266
