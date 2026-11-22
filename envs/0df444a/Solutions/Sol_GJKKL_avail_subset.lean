-- Prove2me | solution 1 for GJKKL.avail_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:35:43.243542+00:00
-- url     : https://prove2.me/submissions/48598cf7-d88b-4968-b06d-7d3e28a67c12

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
theorem _root_.solution (H : Finset (Finset V)) (h : List (Finset V)) : avail H h ⊆ H :=
  filter_subset _ _
end GJKKL
