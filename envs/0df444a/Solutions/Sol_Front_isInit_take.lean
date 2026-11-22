-- Prove2me | solution 1 for Front.isInit_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:17.033188+00:00
-- url     : https://prove2.me/submissions/3c61d1bc-ba6b-4769-9bb2-0088776905ce

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.Widget.Calc
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Theorems.Thm_Front_isInit_nil
attribute [local simp] Front.isInit_nil

set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
namespace Front
theorem _root_.solution (N : ℕ → ℕ) (n : ℕ) : IsInit ((List.range n).map N) N := by
  simp [IsInit]
end Front
