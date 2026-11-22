-- Prove2me | solution 1 for Front.IsInit.head_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:16.608126+00:00
-- url     : https://prove2.me/submissions/157b7ecc-3b65-42a4-a87f-ef26ce6dae25

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
theorem _root_.solution {s : List ℕ} {N : ℕ → ℕ} (hs : IsInit s N) (hne : s ≠ []) :
    s.head? = some (N 0) := by
  have hlen : 0 < s.length := List.length_pos_iff.mpr hne
  obtain ⟨m, hm⟩ : ∃ m, s.length = m + 1 := ⟨s.length - 1, by omega⟩
  rw [hs, hm, List.head?_map, List.range_succ_eq_map]
  simp
end IsInit
end Front
