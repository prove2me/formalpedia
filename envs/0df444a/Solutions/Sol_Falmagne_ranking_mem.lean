-- Prove2me | solution 1 for Falmagne.ranking_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:14.783101+00:00
-- url     : https://prove2.me/submissions/5cc236ce-8239-4b0b-85d1-8f163abe1682

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Basic

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x y : X}
namespace Falmagne
theorem _root_.solution (hl : IsRanking l) (x : X) : x ∈ l := by
  have : x ∈ l.toFinset := by rw [hl.2]; exact Finset.mem_univ x
  simpa using this
end Falmagne
