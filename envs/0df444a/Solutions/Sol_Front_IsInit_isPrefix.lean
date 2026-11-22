-- Prove2me | solution 1 for Front.IsInit.isPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:45.64269+00:00
-- url     : https://prove2.me/submissions/caee1847-2e14-4931-b7e9-0feae6066ee7

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
namespace IsInit
theorem _root_.solution {s t : List ℕ} {N : ℕ → ℕ} (ht : IsInit t N) (h : s <+: t) :
    IsInit s N := by
  change s = (List.range s.length).map N
  calc s = t.take s.length := List.prefix_iff_eq_take.mp h
    _ = ((List.range t.length).map N).take s.length := by rw [← ht]
    _ = (List.range s.length).map N := by
        rw [← List.map_take, List.take_range, Nat.min_eq_left (by simpa using h.length_le)]
end IsInit
end Front
