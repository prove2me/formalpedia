-- Prove2me | solution 1 for GJKKL.IsGreedySeq.toFinset_mem_matchingsOfSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:25.642948+00:00
-- url     : https://prove2.me/submissions/3355d6ad-d08c-4438-a3fb-bbfe30b2dee5

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_IsGreedySeq_subset
public import Theorems.Thm_GJKKL_IsGreedySeq_nodup
public import Theorems.Thm_GJKKL_IsGreedySeq_isMatching
public import Theorems.Thm_GJKKL_mem_matchingsOfSize


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
namespace IsGreedySeq
theorem _root_.solution {H : Finset (Finset V)}
    (hne : ∀ e ∈ H, e.Nonempty) {h : List (Finset V)} (hh : IsGreedySeq H h) :
    h.toFinset ∈ matchingsOfSize H h.length := by
  rw [mem_matchingsOfSize]
  refine ⟨fun e he => hh.subset e (List.mem_toFinset.mp he), hh.isMatching, ?_⟩
  exact List.toFinset_card_of_nodup (hh.nodup hne)
end IsGreedySeq
end GJKKL
