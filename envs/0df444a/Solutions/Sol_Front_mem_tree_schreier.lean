-- Prove2me | solution 1 for Front.mem_tree_schreier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:45:06.552685+00:00
-- url     : https://prove2.me/submissions/46bea715-ea7b-46d7-a1d9-d5ef7fa07cb4

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Theorems.Thm_Front_IsFront_nil_mem_tree
public import Theorems.Thm_Front_exists_extend_len
public import Theorems.Thm_Front_IsInit_head_eq
public import Theorems.Thm_Front_isFront_schreier
public import Theorems.Thm_Front_isInit_nil
public import Theorems.Thm_List_IsPrefix_head_eq
attribute [local simp] Front.isInit_nil



set_option autoImplicit true
@[expose] public section
public section
open Set List Ordinal
universe u
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
namespace Front
theorem _root_.solution (hM : StrictMono M) {s : List ℕ} :
    s ∈ tree (schreier M) ↔
      s.Pairwise (· < ·) ∧ (∀ x ∈ s, x ∈ Set.range M) ∧
        (∀ a, s.head? = some a → s.length ≤ a + 1) := by
  constructor
  · rintro ⟨u, ⟨⟨c, huc, hulen⟩, hup, huM⟩, hpre⟩
    refine ⟨List.Pairwise.sublist hpre.sublist hup, fun x hx => huM x (hpre.subset hx), ?_⟩
    intro a hsa
    have hsne : s ≠ [] := by rintro rfl; simp at hsa
    have huhead : u.head? = some a := by rw [hpre.head_eq hsne]; exact hsa
    have hca : c = a := Option.some.inj (huc.symm.trans huhead)
    calc s.length ≤ u.length := hpre.length_le
      _ = c + 1 := hulen
      _ = a + 1 := by rw [hca]
  · rintro ⟨hs, hsM, hcase⟩
    rcases eq_or_ne s [] with rfl | hne
    · exact (isFront_schreier hM).nil_mem_tree
    · obtain ⟨a, hsa⟩ : ∃ a, s.head? = some a := by
        cases s with
        | nil => exact absurd rfl hne
        | cons c t => exact ⟨c, rfl⟩
      have hlen : s.length ≤ a + 1 := hcase a hsa
      obtain ⟨t, hpre, ht, htM, htlen⟩ := exists_extend_len hM (a + 1) s hs hsM hlen
      have hthead : t.head? = some a := by rw [hpre.head_eq hne]; exact hsa
      exact ⟨t, ⟨⟨a, hthead, htlen⟩, ht, htM⟩, hpre⟩
end Front
