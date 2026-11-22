-- Prove2me | solution 1 for GJKKL.dv_cons_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:27:14.24782+00:00
-- url     : https://prove2.me/submissions/8d29bb22-e2da-440d-b429-3cb638bc6628

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Theorems.Thm_GJKKL_dv_cons

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (a : Finset V) (h : List (Finset V)) (v : V) :
    dv H (a :: h) v ≤ dv H h v := by
  have := dv_cons H a h v; omega
end GJKKL
