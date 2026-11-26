-- Prove2me | solution 1 for Falmagne.rankingChoice_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:14.250177+00:00
-- url     : https://prove2.me/submissions/83fd6781-8fb5-48b4-9d25-8eb14561bfa9

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Basic
public import Theorems.Thm_Falmagne_mem_lowerContour
attribute [local simp] Falmagne.mem_lowerContour

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x y : X}
namespace Falmagne
theorem _root_.solution :
    rankingChoice l A x = 1 ↔ x ∈ A ∧ A ⊆ lowerContour l x := by
  simp [rankingChoice]
end Falmagne
