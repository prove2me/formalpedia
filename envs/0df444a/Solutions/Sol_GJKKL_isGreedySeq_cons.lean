-- Prove2me | solution 1 for GJKKL.isGreedySeq_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:35:24.590896+00:00
-- url     : https://prove2.me/submissions/750f751c-425c-4d35-b580-148d763917ba

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
theorem _root_.solution {H : Finset (Finset V)} {a : Finset V} {h : List (Finset V)} :
    IsGreedySeq H (a :: h) ↔ IsGreedySeq H h ∧ a ∈ avail H h := Iff.rfl
end GJKKL
