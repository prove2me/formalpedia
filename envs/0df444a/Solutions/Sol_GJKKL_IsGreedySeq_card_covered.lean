-- Prove2me | solution 1 for GJKKL.IsGreedySeq.card_covered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:31.644886+00:00
-- url     : https://prove2.me/submissions/5e12a246-1c01-4269-870f-b54a9432283c

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_avail_subset
public import Theorems.Thm_GJKKL_mem_covered
public import Theorems.Thm_GJKKL_mem_avail_iff_uncovered
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
theorem _root_.solution {H : Finset (Finset V)} {k : ℕ} (hk : IsUniform H k) :
    ∀ {h : List (Finset V)}, IsGreedySeq H h → (covered h).card = k * h.length
  | [], _ => by simp [covered]
  | a :: h, hh => by
    have hcov : covered (a :: h) = a ∪ covered h := by
      ext v; simp [mem_covered]
    have hdisj : Disjoint a (covered h) := (mem_avail_iff_uncovered.mp hh.2).2
    rw [hcov, card_union_of_disjoint hdisj, solution hk hh.1,
      hk a (avail_subset H h hh.2), List.length_cons]
    ring
end IsGreedySeq
end GJKKL
