-- Prove2me | solution 1 for Front.IsInit.prefix_or_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:48.211178+00:00
-- url     : https://prove2.me/submissions/544e1567-d430-4b74-8961-c26c332a3a49

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
public import Theorems.Thm_Front_range_prefix_range

set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
namespace Front
namespace IsInit
theorem _root_.solution {s t : List ℕ} {N : ℕ → ℕ}
    (hs : IsInit s N) (ht : IsInit t N) : s <+: t ∨ t <+: s := by
  rcases le_total s.length t.length with h | h
  · left;  rw [hs, ht]; exact (range_prefix_range h).map N
  · right; rw [hs, ht]; exact (range_prefix_range h).map N
end IsInit
end Front
