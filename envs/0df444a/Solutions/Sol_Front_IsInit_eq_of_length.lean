-- Prove2me | solution 1 for Front.IsInit.eq_of_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:41:49.314053+00:00
-- url     : https://prove2.me/submissions/9b252e88-f880-4634-a267-3b43f8bbf552

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
namespace IsInit
theorem _root_.solution {s t : List ℕ} {N : ℕ → ℕ}
    (hs : IsInit s N) (ht : IsInit t N) (h : s.length = t.length) : s = t := by
  rw [hs, ht, h]
end IsInit
end Front
