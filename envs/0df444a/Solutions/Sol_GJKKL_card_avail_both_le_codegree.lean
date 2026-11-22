-- Prove2me | solution 1 for GJKKL.card_avail_both_le_codegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:29.278207+00:00
-- url     : https://prove2.me/submissions/ddba6b71-287f-4013-baa7-c9615dbf5cb9

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Theorems.Thm_GJKKL_avail_subset


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (h : List (Finset V)) (u w : V) :
    ((avail H h).filter (fun e => u ∈ e ∧ w ∈ e)).card ≤ codegree H u w :=
  card_le_card (filter_subset_filter _ (avail_subset H h))
end GJKKL
