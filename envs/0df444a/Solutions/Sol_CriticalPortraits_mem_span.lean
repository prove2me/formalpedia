-- Prove2me | solution 1 for CriticalPortraits.mem_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:50.431825+00:00
-- url     : https://prove2.me/submissions/cb41eade-5e9b-4b68-8ffc-61f108be074b

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Theorems.Thm_CriticalPortraits_maxVal_ge
public import Theorems.Thm_CriticalPortraits_minVal_le


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {N : ℕ} {S : Finset (ZMod N)} (h : S.Nonempty) {x : ZMod N} (hx : x ∈ S) :
    spanLo S h ≤ x.val ∧ x.val ≤ spanHi S h :=
  ⟨minVal_le S h x hx, maxVal_ge S h x hx⟩
end CriticalPortraits
