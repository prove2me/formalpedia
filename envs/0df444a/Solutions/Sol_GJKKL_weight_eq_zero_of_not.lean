-- Prove2me | solution 1 for GJKKL.weight_eq_zero_of_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:55.334871+00:00
-- url     : https://prove2.me/submissions/fe6e81bb-af0a-4e21-b4d9-7f1be1b933fd

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_weight_pos_iff
public import Theorems.Thm_GJKKL_History_weight_nonneg


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution {H : Finset (Finset V)} {h : List (Finset V)}
    (hh : ¬ IsGreedySeq H h) : weight (greedyKernel H) h = 0 := by
  rcases (weight_nonneg (greedyKernel H) h).lt_or_eq with hlt | heq
  · exact absurd (weight_pos_iff.mp hlt) hh
  · exact heq.symm
end GJKKL
