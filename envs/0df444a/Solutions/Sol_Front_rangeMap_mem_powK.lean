-- Prove2me | solution 1 for Front.rangeMap_mem_powK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:18.034195+00:00
-- url     : https://prove2.me/submissions/ab002048-1050-4092-a485-bb5e41cdd11c

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
theorem _root_.solution {M : ℕ → ℕ} (hM : StrictMono M) {e : ℕ → ℕ}
    (he : StrictMono e) (k : ℕ) : (List.range k).map (M ∘ e) ∈ powK M k := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun hab => (hM.comp he) hab
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact ⟨e i, rfl⟩
end Front
