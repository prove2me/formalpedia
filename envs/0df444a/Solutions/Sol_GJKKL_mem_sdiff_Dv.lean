-- Prove2me | solution 1 for GJKKL.mem_sdiff_Dv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:39:37.274792+00:00
-- url     : https://prove2.me/submissions/f8adafde-921d-45b0-bcf9-4531ad4ffe0d

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
public import Theorems.Thm_GJKKL_mem_Dv
attribute [local simp] GJKKL.Dv_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution {H : Finset (Finset V)} {h : List (Finset V)} {v : V} {a : Finset V} :
    a ∈ avail H h \ Dv H h v ↔ a ∈ avail H h ∧ v ∉ a := by
  simp only [mem_sdiff, mem_Dv]; tauto
end GJKKL
