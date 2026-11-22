-- Prove2me | solution 1 for Front.isInit_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:41:47.961113+00:00
-- url     : https://prove2.me/submissions/2400806f-baea-45a0-97e2-84a62d612bf8

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

set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
namespace Front
theorem _root_.solution (N : ℕ → ℕ) : IsInit [] N := by simp [IsInit]
end Front
