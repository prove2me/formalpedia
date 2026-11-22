-- Prove2me | solution 1 for GJKKL.IsGreedySeq.isMatching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:59.106799+00:00
-- url     : https://prove2.me/submissions/5ea5be5d-c84c-4919-9d2a-6a9d2d2600af

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_IsGreedySeq_pairwise
public import Theorems.Thm_GJKKL_disjoint_of_pairwise

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
namespace IsGreedySeq
theorem _root_.solution {H : Finset (Finset V)} {h : List (Finset V)}
    (hh : IsGreedySeq H h) : IsMatching h.toFinset := by
  intro e he f hf hef
  rw [List.mem_toFinset] at he hf
  exact disjoint_of_pairwise hh.pairwise he hf hef
end IsGreedySeq
end GJKKL
