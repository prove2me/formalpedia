-- Prove2me | solution 1 for Front.range_prefix_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:41:59.016177+00:00
-- url     : https://prove2.me/submissions/f8cd64d3-4a25-4437-a5c5-504aa3c8a4af

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
theorem _root_.solution {m n : ℕ} (h : m ≤ n) : List.range m <+: List.range n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add]
  exact List.prefix_append _ _
end Front
