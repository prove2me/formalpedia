-- Prove2me | solution 1 for Front.IsInit.getElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:24.353485+00:00
-- url     : https://prove2.me/submissions/e4603f64-be6f-413d-91de-7a59bc53e36f

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
theorem _root_.solution {s : List ℕ} {N : ℕ → ℕ} (hs : IsInit s N)
    {i : ℕ} (h : i < s.length) : s[i] = N i := by
  have hq : s[i]? = some (N i) := by
    conv_lhs => rw [hs]
    simp [h]
  simpa [List.getElem?_eq_getElem h] using hq
end IsInit
end Front
