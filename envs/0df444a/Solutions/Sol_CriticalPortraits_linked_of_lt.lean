-- Prove2me | solution 1 for CriticalPortraits.linked_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:46.428912+00:00
-- url     : https://prove2.me/submissions/00f234a7-5ce2-40af-a6ee-d9a08323ba97

module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {N : ℕ} {A B : Finset (ZMod N)} {a1 a2 b1 b2 : ZMod N}
    (ha1 : a1 ∈ A) (ha2 : a2 ∈ A) (hb1 : b1 ∈ B) (hb2 : b2 ∈ B)
    (h1 : a1.val < b1.val) (h2 : b1.val < a2.val) (h3 : a2.val < b2.val) :
    Linked A B :=
  ⟨a1, ha1, a2, ha2, b1, hb1, b2, hb2, Or.inl ⟨h1, h2, h3⟩⟩
end CriticalPortraits
