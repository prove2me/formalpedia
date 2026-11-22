-- Prove2me | solution 1 for GJKKL.Dv_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:28.240125+00:00
-- url     : https://prove2.me/submissions/fde64979-b406-4f0d-9fc9-00826f1fd8af

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
theorem _root_.solution (H : Finset (Finset V)) (h : List (Finset V)) (v : V) :
    Dv H h v ⊆ H.filter (fun e => v ∈ e) :=
  filter_subset_filter _ (avail_subset H h)
end GJKKL
