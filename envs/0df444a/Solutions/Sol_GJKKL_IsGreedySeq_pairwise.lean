-- Prove2me | solution 1 for GJKKL.IsGreedySeq.pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:53.797846+00:00
-- url     : https://prove2.me/submissions/6951e0d5-f823-4e4e-bc46-e71e9f152508

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
namespace IsGreedySeq
theorem _root_.solution {H : Finset (Finset V)} :
    ∀ {h : List (Finset V)}, IsGreedySeq H h → h.Pairwise Disjoint
  | [], _ => List.Pairwise.nil
  | a :: h, hh => List.Pairwise.cons (fun f hf => (mem_avail.mp hh.2).2 f hf)
      (solution hh.1)
end IsGreedySeq
end GJKKL
