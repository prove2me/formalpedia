-- Prove2me | solution 1 for GJKKL.dv_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:26.589293+00:00
-- url     : https://prove2.me/submissions/93fb4909-0b43-4388-9a99-e146f7e33b29

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Theorems.Thm_GJKKL_Dv_cons

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (a : Finset V) (h : List (Finset V)) (v : V) :
    dv H (a :: h) v + ((Dv H h v).filter (fun e => ¬ Disjoint e a)).card = dv H h v := by
  rw [dv, Dv_cons, dv]
  exact card_filter_add_card_filter_not _
end GJKKL
