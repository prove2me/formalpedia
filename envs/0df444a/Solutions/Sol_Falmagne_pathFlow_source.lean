-- Prove2me | solution 1 for Falmagne.pathFlow_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:55.211825+00:00
-- url     : https://prove2.me/submissions/7c6a96a0-51cf-45bc-9469-4b996f04c6af

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Path
public import Theorems.Thm_Falmagne_pathFlow_nil
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_divergence
attribute [local simp] Falmagne.pathFlow_nil
attribute [local simp] Falmagne.pathFlow_cons

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace Falmagne
theorem _root_.solution (l : List X) (hl : l.Nodup) (hfull : l.toFinset = Finset.univ)
    [Nonempty X] : outflow (pathFlow l) Finset.univ = 1 := by
  have h := pathFlow_divergence l hl Finset.univ
  have hn : (Finset.univ : Finset X) ≠ ∅ := Finset.univ_nonempty.ne_empty
  simpa [inflow, hfull, hn] using h
end Falmagne
