-- Prove2me | solution 1 for GJKKL.dv_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:27:19.52382+00:00
-- url     : https://prove2.me/submissions/1e8ace19-a403-4b85-81d1-6c9a125d999f

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Theorems.Thm_GJKKL_Dv_subset

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (h : List (Finset V)) (v : V) :
    dv H h v ≤ degree H v :=
  card_le_card (Dv_subset H h v)
end GJKKL
