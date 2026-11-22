-- Prove2me | solution 1 for Front.isFront_schreier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:47.21649+00:00
-- url     : https://prove2.me/submissions/9c6fffbb-29b8-43d2-85b2-5434dbd91b1f

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
public import Theorems.Thm_List_IsPrefix_head_eq
public import Theorems.Thm_Front_isInit_nil
public import Theorems.Thm_Front_isInit_take
public import Theorems.Thm_Front_IsInit_head_eq
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
theorem _root_.solution {M : ℕ → ℕ} (hM : StrictMono M) : IsFront (schreier M) M where
  mono := hM
  sorted _ hs := hs.2.1
  subM _ hs := hs.2.2
  incomp s hs t ht hst := by
    obtain ⟨a, hsa, hslen⟩ := hs.1
    obtain ⟨b, htb, htlen⟩ := ht.1
    have hsne : s ≠ [] := by rintro rfl; simp at hsa
    have hth : t.head? = some a := by rw [hst.head_eq hsne]; exact hsa
    have hab : a = b := Option.some.inj (hth.symm.trans htb)
    exact hst.eq_of_length (by rw [hslen, htlen, hab])
  dense g hg := by
    -- the initial segment of `M ∘ g` whose length is `(M ∘ g) 0 + 1`
    refine ⟨(List.range ((M ∘ g) 0 + 1)).map (M ∘ g), ⟨?_, ?_, ?_⟩,
      isInit_take (M ∘ g) _⟩
    · exact ⟨(M ∘ g) 0, (isInit_take (M ∘ g) ((M ∘ g) 0 + 1)).head_eq (by simp), by simp⟩
    · exact (rangeMap_mem_powK hM hg _).2.1
    · exact (rangeMap_mem_powK hM hg _).2.2
  base := by
    right
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨s, hs, hxs⟩
      exact hs.2.2 x hxs
    · rintro ⟨i, rfl⟩
      have he : StrictMono (i + ·) := add_right_strictMono
      refine ⟨(List.range (M i + 1)).map (M ∘ (i + ·)), ⟨?_, ?_, ?_⟩, ?_⟩
      · exact ⟨M i, (isInit_take (M ∘ (i + ·)) (M i + 1)).head_eq (by simp), by simp⟩
      · exact (rangeMap_mem_powK hM he _).2.1
      · exact (rangeMap_mem_powK hM he _).2.2
      · rw [List.mem_map]
        exact ⟨0, List.mem_range.mpr (by omega), by simp⟩
end Front
