-- Prove2me | solution 1 for Erdos684.smallPrimePart_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:39:52.242255+00:00
-- url     : https://prove2.me/submissions/a2ab385e-c66d-4731-ba05-b7cd580a17e0

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution (n k : ℕ) : 0 < smallPrimePart n k := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primesLE hp).pos _
end Erdos684
