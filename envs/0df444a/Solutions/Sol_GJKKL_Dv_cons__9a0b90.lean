-- Prove2me | solution 1 for GJKKL.Dv_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:34.76481+00:00
-- url     : https://prove2.me/submissions/54792df4-6003-49aa-a987-761acb523238

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Theorems.Thm_GJKKL_mem_Dv
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_avail_cons
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil


attribute [local simp] GJKKL.Dv_nil

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (a : Finset V) (h : List (Finset V)) (v : V) :
    Dv H (a :: h) v = (Dv H h v).filter (fun e => Disjoint e a) := by
  ext e
  simp only [mem_Dv, avail_cons, mem_filter]
  tauto
end GJKKL
