-- Prove2me | solution 1 for Front.exists_extend_len
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:31.548693+00:00
-- url     : https://prove2.me/submissions/26ed93b2-82f9-4551-ad3c-1c8830ea10fe

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Theorems.Thm_Front_exists_extend_gt
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
theorem _root_.solution (hM : StrictMono M) (L : ℕ) :
    ∀ (s : List ℕ), s.Pairwise (· < ·) → (∀ x ∈ s, x ∈ Set.range M) →
      s.length ≤ L → ∃ t, s <+: t ∧ t.Pairwise (· < ·) ∧
        (∀ x ∈ t, x ∈ Set.range M) ∧ t.length = L := by
  suffices H : ∀ d s, s.Pairwise (· < ·) → (∀ x ∈ s, x ∈ Set.range M) →
      L - s.length = d → s.length ≤ L → ∃ t, s <+: t ∧ t.Pairwise (· < ·) ∧
        (∀ x ∈ t, x ∈ Set.range M) ∧ t.length = L by
    intro s hs hsM hL; exact H _ s hs hsM rfl hL
  intro d
  induction d with
  | zero => intro s hs hsM hd hL; exact ⟨s, List.prefix_rfl, hs, hsM, by omega⟩
  | succ e ih =>
    intro s hs hsM hd hL
    obtain ⟨x, hxM, hxgt⟩ := exists_extend_gt hM s
    have hs' : (s ++ [x]).Pairwise (· < ·) := by
      rw [List.pairwise_append]
      refine ⟨hs, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; exact hxgt a ha
    have hs'M : ∀ z ∈ s ++ [x], z ∈ Set.range M := by
      intro z hz; rw [List.mem_append] at hz
      rcases hz with h | h
      · exact hsM z h
      · simp only [List.mem_singleton] at h; subst h; exact hxM
    obtain ⟨t, hpre, ht, htM, htlen⟩ := ih (s ++ [x]) hs' hs'M (by simp; omega) (by simp; omega)
    exact ⟨t, (List.prefix_append s [x]).trans hpre, ht, htM, htlen⟩
end Front
