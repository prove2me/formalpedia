-- Prove2me | solution 1 for GJKKL.IsGreedySeq.nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:34.646717+00:00
-- url     : https://prove2.me/submissions/d3a38aaf-4501-4b78-a26a-965bdb33ead6

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_IsGreedySeq_subset
public import Theorems.Thm_GJKKL_IsGreedySeq_pairwise

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
namespace IsGreedySeq
theorem _root_.solution {H : Finset (Finset V)} (hne : ∀ e ∈ H, e.Nonempty)
    {h : List (Finset V)} (hh : IsGreedySeq H h) : h.Nodup := by
  refine hh.pairwise.imp_of_mem fun {a b} ha _ hab => ?_
  rintro rfl
  obtain ⟨v, hv⟩ := hne a (hh.subset a ha)
  exact Finset.disjoint_left.mp hab hv hv
end IsGreedySeq
end GJKKL
