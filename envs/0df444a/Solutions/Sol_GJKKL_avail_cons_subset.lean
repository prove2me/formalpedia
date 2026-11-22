-- Prove2me | solution 1 for GJKKL.avail_cons_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:26:46.669932+00:00
-- url     : https://prove2.me/submissions/d753a904-ceca-49dc-8e6d-e8fdeb875034

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_avail_cons

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (a : Finset V) (h : List (Finset V)) :
    avail H (a :: h) ⊆ avail H h := by
  rw [avail_cons]; exact filter_subset _ _
end GJKKL
