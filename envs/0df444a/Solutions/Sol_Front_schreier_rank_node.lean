-- Prove2me | solution 1 for Front.schreier_rank_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:45:53.597983+00:00
-- url     : https://prove2.me/submissions/f2a5ce3e-4d5b-4722-88ed-c10d42c6fd84

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Theorems.Thm_Front_exists_extend_gt
public import Theorems.Thm_Front_rank_eq_sub
public import Theorems.Thm_Front_mem_tree_schreier
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
theorem _root_.solution (hM : StrictMono M) {s : List ℕ} {a : ℕ}
    (hsmem : s ∈ tree (schreier M)) (hhead : s.head? = some a) :
    letI : IsWellFounded (List ℕ) (treeExt (schreier M)) :=
      ⟨(isFront_schreier hM).wellFounded_treeExt⟩
    IsWellFounded.rank (treeExt (schreier M)) s = ((a + 1 - s.length : ℕ) : Ordinal) := by
  letI : IsWellFounded (List ℕ) (treeExt (schreier M)) :=
    ⟨(isFront_schreier hM).wellFounded_treeExt⟩
  have hpre_a : [a] <+: s := by
    obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp hhead
    exact ⟨ys, rfl⟩
  have hhead' : ∀ s', [a] <+: s' → s'.head? = some a := by
    intro s' hp
    rw [hp.head_eq (by simp), List.head?_cons]
  have hbound : ∀ s', [a] <+: s' → s' ∈ tree (schreier M) → s'.length ≤ a + 1 :=
    fun s' hp hmem => ((mem_tree_schreier hM).mp hmem).2.2 a (hhead' s' hp)
  have hext : ∀ s', [a] <+: s' → s' ∈ tree (schreier M) → s'.length < a + 1 →
      ∃ x, treeExt (schreier M) (s' ++ [x]) s' := by
    intro s' hp hmem hlt
    obtain ⟨hsp, hsM, -⟩ := (mem_tree_schreier hM).mp hmem
    have hne' : s' ≠ [] := by rintro rfl; simpa using hp.length_le
    obtain ⟨x, hxM, hxgt⟩ := exists_extend_gt hM s'
    have hs'p : (s' ++ [x]).Pairwise (· < ·) := by
      rw [List.pairwise_append]
      refine ⟨hsp, List.pairwise_singleton _ _, ?_⟩
      intro c hc b hb; simp only [List.mem_singleton] at hb; subst hb; exact hxgt c hc
    have hs'M : ∀ z ∈ s' ++ [x], z ∈ Set.range M := by
      intro z hz; rw [List.mem_append] at hz
      rcases hz with h | h
      · exact hsM z h
      · simp only [List.mem_singleton] at h; subst h; exact hxM
    have hs'head : (s' ++ [x]).head? = some a := by
      rw [(List.prefix_append s' [x]).head_eq hne']; exact hhead' s' hp
    refine ⟨x, (mem_tree_schreier hM).mpr ⟨hs'p, hs'M, ?_⟩, hmem,
      List.prefix_append s' [x], ?_⟩
    · intro c hc
      rw [hs'head] at hc
      obtain rfl := Option.some.inj hc
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro h; have := congrArg List.length h; simp at this
  exact rank_eq_sub (isFront_schreier hM) (a + 1) hbound hext s hpre_a hsmem
end Front
