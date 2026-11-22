-- Prove2me | solution 1 for Front.powK_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:45:41.941008+00:00
-- url     : https://prove2.me/submissions/933b1290-5e62-4b23-9874-458cfe1b1d02

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Theorems.Thm_Front_IsFront_nil_mem_tree
public import Theorems.Thm_Front_exists_extend_gt
public import Theorems.Thm_Front_rank_eq_sub
public import Theorems.Thm_Front_mem_tree_powK
public import Theorems.Thm_Front_isFront_powK
public import Theorems.Thm_Front_isInit_nil
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
theorem _root_.solution (hM : StrictMono M) (k : ℕ) : (isFront_powK hM k).rank = (k : Ordinal) := by
  have hb : ∀ s, ([] : List ℕ) <+: s → s ∈ tree (powK M k) → s.length ≤ k :=
    fun s _ hs => ((mem_tree_powK hM).mp hs).2.2
  have he : ∀ s, ([] : List ℕ) <+: s → s ∈ tree (powK M k) → s.length < k →
      ∃ x, treeExt (powK M k) (s ++ [x]) s := by
    intro s _ hs hlt
    obtain ⟨hsp, hsM, -⟩ := (mem_tree_powK hM).mp hs
    obtain ⟨x, hxM, hxgt⟩ := exists_extend_gt hM s
    have hs'p : (s ++ [x]).Pairwise (· < ·) := by
      rw [List.pairwise_append]
      refine ⟨hsp, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; exact hxgt a ha
    have hs'M : ∀ z ∈ s ++ [x], z ∈ Set.range M := by
      intro z hz; rw [List.mem_append] at hz
      rcases hz with h | h
      · exact hsM z h
      · simp only [List.mem_singleton] at h; subst h; exact hxM
    refine ⟨x, (mem_tree_powK hM).mpr ⟨hs'p, hs'M, by simp; omega⟩, hs,
      List.prefix_append s [x], ?_⟩
    intro h; have := congrArg List.length h; simp at this
  have := rank_eq_sub (isFront_powK hM k) k hb he [] List.nil_prefix
    (isFront_powK hM k).nil_mem_tree
  simpa [IsFront.rank] using this
end Front
