-- Prove2me | solution 1 for Front.isFront_powK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:47.734115+00:00
-- url     : https://prove2.me/submissions/674f22f3-3b84-4e26-8e44-177a2fd26943

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
public import Theorems.Thm_Front_isInit_take
public import Theorems.Thm_Front_IsInit_eq_of_length
public import Theorems.Thm_Front_rangeMap_mem_powK
attribute [local simp] Front.isInit_nil

set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
namespace Front
theorem _root_.solution {M : ℕ → ℕ} (hM : StrictMono M) (k : ℕ) : IsFront (powK M k) M where
  mono := hM
  sorted _ hs := hs.2.1
  subM _ hs := hs.2.2
  incomp _ hs _ ht hst := hst.eq_of_length (by rw [hs.1, ht.1])
  dense g hg :=
    ⟨(List.range k).map (M ∘ g), rangeMap_mem_powK hM hg k, isInit_take (M ∘ g) k⟩
  base := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · -- `[M]^0 = {∅}`
      left
      subst hk
      ext s
      simp only [powK, Set.mem_ofPred_eq, Set.mem_singleton_iff, List.length_eq_zero_iff]
      constructor
      · rintro ⟨h, -, -⟩; exact h
      · rintro rfl; exact ⟨rfl, List.Pairwise.nil, by simp⟩
    · -- `k ≥ 1`: the elements of `[M]^k` cover `M`
      right
      ext x
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨s, hs, hxs⟩
        exact hs.2.2 x hxs
      · rintro ⟨i, rfl⟩
        refine ⟨(List.range k).map (M ∘ (i + ·)),
          rangeMap_mem_powK hM (add_right_strictMono) k, ?_⟩
        rw [List.mem_map]
        exact ⟨0, List.mem_range.mpr hk, by simp⟩
end Front
