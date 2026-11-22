-- Prove2me | solution 1 for GJKKL.IsGreedySeq.subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:53.33702+00:00
-- url     : https://prove2.me/submissions/eadba815-644b-44fe-b2bb-bcadd5bc5486

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_avail_subset
public import Theorems.Thm_GJKKL_isGreedySeq_nil
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil


attribute [local simp] GJKKL.isGreedySeq_nil
attribute [local simp] GJKKL.isGreedySeq_cons

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
namespace IsGreedySeq
theorem _root_.solution {H : Finset (Finset V)} :
    ∀ {h : List (Finset V)}, IsGreedySeq H h → ∀ f ∈ h, f ∈ H
  | [], _ => by simp
  | a :: h, hh => by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact avail_subset H h hh.2
    · exact solution hh.1 f hf
end IsGreedySeq
end GJKKL
