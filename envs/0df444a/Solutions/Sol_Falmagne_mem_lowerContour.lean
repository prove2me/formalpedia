-- Prove2me | solution 1 for Falmagne.mem_lowerContour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:04.450969+00:00
-- url     : https://prove2.me/submissions/821ed9db-1087-4991-b195-127607ef6d6b

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
theorem _root_.solution (l : List X) (x y : X) :
    y ∈ lowerContour l x ↔ y ∈ l ∧ l.idxOf x ≤ l.idxOf y := by
  simp [lowerContour]
end Falmagne
