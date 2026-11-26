-- Prove2me | solution 1 for Falmagne.pathFlow_conserve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:01.581823+00:00
-- url     : https://prove2.me/submissions/8e122ae9-1543-4bfb-823e-234bef7e5c88

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
    (A : Finset X) (hA : A.Nonempty) (hU : A ≠ Finset.univ) :
    outflow (pathFlow l) A = inflow (pathFlow l) A := by
  have h := pathFlow_divergence l hl A
  have hz : outflow (pathFlow l) A - inflow (pathFlow l) A = 0 := by
    simpa [hfull, hU, hA.ne_empty] using h
  exact sub_eq_zero.mp hz
end Falmagne
