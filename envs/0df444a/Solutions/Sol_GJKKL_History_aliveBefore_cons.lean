-- Prove2me | solution 1 for GJKKL.History.aliveBefore_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:31.996857+00:00
-- url     : https://prove2.me/submissions/c526b581-7e23-4f05-989a-fd10bbdec377

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_History_Freedman

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace GJKKL.History
theorem _root_.solution (G : List α → Prop) (a : α) (h : List α) :
    AliveBefore G (a :: h) ↔ AliveBefore G h ∧ G h := Iff.rfl
end GJKKL.History
