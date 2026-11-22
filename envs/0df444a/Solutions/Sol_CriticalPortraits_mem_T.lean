-- Prove2me | solution 1 for CriticalPortraits.mem_T
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:43.534677+00:00
-- url     : https://prove2.me/submissions/96157391-b272-404b-b90a-7d3befba1ba2

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
theorem _root_.solution {N : ℕ} {P : Finset (Finset (ZMod N))} {x : ZMod N} :
    x ∈ T P ↔ ∃ S ∈ P, x ∈ eraseMin S := by
  unfold T
  rw [Finset.mem_sup]
end CriticalPortraits
