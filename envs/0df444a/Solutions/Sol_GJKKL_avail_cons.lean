-- Prove2me | solution 1 for GJKKL.avail_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:37:07.117583+00:00
-- url     : https://prove2.me/submissions/90d695d0-5846-43f4-83d5-2b6aa132cdfd

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (a : Finset V) (h : List (Finset V)) :
    avail H (a :: h) = (avail H h).filter (fun e => Disjoint e a) := by
  ext e
  simp only [mem_avail, List.mem_cons, forall_eq_or_imp, mem_filter]
  tauto
end GJKKL
