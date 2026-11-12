-- Prove2me | solution 1 for ConantTerry.Orders.tree_ramsey
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:21:49.457926+00:00
-- url     : https://prove2.me/submissions/df9e81a2-aa58-464f-bd90-17a2d616d2f6

import Mathlib
import Definitions.Def_ConantTerry_Orders_tree_embeddings

section
set_option autoImplicit false
namespace ConantTerry.Dev.TR
open ConantTerry.Orders

theorem sum_update_aux {m : ℕ} (h : Fin m → ℕ) (i0 : Fin m) (hi : 2 ≤ h i0) :
    (∑ i, h i) = (∑ i, Function.update h i0 (h i0 - 1) i) + 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i0), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase _ h (Finset.mem_univ i0)]
  omega

theorem sum_ge_aux {m : ℕ} (h : Fin m → ℕ) (i0 : Fin m) (hpos : ∀ i, 1 ≤ h i) :
    (∑ i, h i) ≥ m - 1 + h i0 := by
  rw [← Finset.add_sum_erase _ h (Finset.mem_univ i0)]
  have : (∑ i ∈ Finset.univ.erase i0, 1) ≤ ∑ i ∈ Finset.univ.erase i0, h i :=
    Finset.sum_le_sum (fun i _ => hpos i)
  simp [Finset.card_erase_of_mem] at this
  omega

theorem ramsey_aux : ∀ (t : ℕ) (m : ℕ) (h : Fin m → ℕ) (C : Fin m → Set (List Bool)),
    1 ≤ t → (∀ i, 1 ≤ h i) → t + m = (∑ i, h i) + 1 →
    (∀ σ : List Bool, σ.length < t → ∃ i, σ ∈ C i) →
    ∃ (i : Fin m) (g : List Bool → List Bool),
      (∀ σ : List Bool, σ.length < h i → (g σ).length < t ∧ g σ ∈ C i) ∧
      (∀ (σ τ : List Bool) (a : Bool), σ.length < h i → τ.length < h i →
        σ ++ [a] <+: τ → g σ ++ [a] <+: g τ) := by
  intro t
  induction t with
  | zero => intro m h C h1; omega
  | succ n ih =>
    intro m h C _ hpos hsum hcov
    obtain ⟨i0, hi0⟩ := hcov [] (by simp)
    by_cases h1 : h i0 = 1
    · refine ⟨i0, fun _ => [], ?_, ?_⟩
      · intro σ hσ
        exact ⟨by simpa using Nat.succ_pos n, by simpa using hi0⟩
      · intro σ τ a hσ hτ hp
        have := hp.length_le
        simp at this
        omega
    · have h2 : 2 ≤ h i0 := by have := hpos i0; omega
      have hge := sum_ge_aux h i0 hpos
      have hn : 1 ≤ n := by omega
      have hs' := sum_update_aux h i0 h2
      set h' := Function.update h i0 (h i0 - 1) with hh'
      have hpos' : ∀ i, 1 ≤ h' i := by
        intro i
        by_cases hi : i = i0
        · subst hi; simp [hh']; omega
        · simp [hh', hi]; exact hpos i
      have H : ∀ u : Bool, ∃ (i : Fin m) (g : List Bool → List Bool),
          (∀ σ : List Bool, σ.length < h' i → (g σ).length < n ∧ u :: g σ ∈ C i) ∧
          (∀ (σ τ : List Bool) (a : Bool), σ.length < h' i → τ.length < h' i →
            σ ++ [a] <+: τ → g σ ++ [a] <+: g τ) := by
        intro u
        exact ih m h' (fun i => {σ | u :: σ ∈ C i}) hn hpos' (by omega)
          (fun σ hσ => hcov (u :: σ) (by simpa using hσ))
      choose I G hG using H
      by_cases hex : ∃ u, I u ≠ i0
      · obtain ⟨u, hu⟩ := hex
        have hh : h' (I u) = h (I u) := by simp [hh', hu]
        obtain ⟨hG1, hG2⟩ := hG u
        refine ⟨I u, fun σ => u :: G u σ, ?_, ?_⟩
        · intro σ hσ
          rw [← hh] at hσ
          obtain ⟨a1, a2⟩ := hG1 σ hσ
          exact ⟨by simpa using a1, a2⟩
        · intro σ τ a hσ hτ hp
          rw [← hh] at hσ hτ
          have := hG2 σ τ a hσ hτ hp
          simpa using this
      · push_neg at hex
        have hh : h' i0 = h i0 - 1 := by simp [hh']
        refine ⟨i0, fun σ => match σ with | [] => [] | u :: σ' => u :: G u σ', ?_, ?_⟩
        · intro σ hσ
          cases σ with
          | nil => exact ⟨by simp, hi0⟩
          | cons u σ' =>
            have hσ' : σ'.length < h' (I u) := by
              rw [hex u, hh]; simp at hσ; omega
            obtain ⟨a1, a2⟩ := hG u |>.1 σ' hσ'
            rw [hex u] at a2
            exact ⟨by simpa using a1, a2⟩
        · intro σ τ a hσ hτ hp
          cases σ with
          | nil =>
            cases τ with
            | nil => simp at hp
            | cons b τ' =>
              simp at hp
              obtain ⟨rfl, -⟩ := hp
              simp
          | cons u σ' =>
            cases τ with
            | nil => simp at hp
            | cons b τ' =>
              simp at hp
              obtain ⟨rfl, hp'⟩ := hp
              have hσ' : σ'.length < h' (I u) := by
                rw [hex u, hh]; simp at hσ; omega
              have hτ' : τ'.length < h' (I u) := by
                rw [hex u, hh]; simp at hτ; omega
              have := (hG u).2 σ' τ' a hσ' hτ' hp'
              simpa using this

end ConantTerry.Dev.TR

namespace ConantTerry.Orders
open ConantTerry.Dev.TR in
theorem chk_tree_ramsey (m t : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t)
    (heights : Fin m → ℕ) (hpos : ∀ i, 1 ≤ heights i)
    (hsum : t + m = (∑ i : Fin m, heights i) + 1)
    (C : Fin m → Set (WordsBelow t))
    (hcover : ∀ σ : WordsBelow t, ∃ i : Fin m, σ ∈ C i) :
    ∃ (i : Fin m) (φ : WordsBelow (heights i) → WordsBelow t),
      IsTreeEmbedding φ ∧ Set.range φ ⊆ C i := by
  obtain ⟨i, g, hg1, hg2⟩ := ramsey_aux t m heights
    (fun i => {σ | ∃ h : σ.length < t, (⟨σ, h⟩ : WordsBelow t) ∈ C i}) ht hpos hsum
    (fun σ hσ => by
      obtain ⟨i, hi⟩ := hcover ⟨σ, hσ⟩
      exact ⟨i, hσ, hi⟩)
  refine ⟨i, fun σ => ⟨g σ.val, (hg1 σ.val σ.2).1⟩, ?_, ?_⟩
  · intro σ τ a hp
    exact hg2 σ.val τ.val a σ.2 τ.2 hp
  · rintro _ ⟨σ, rfl⟩
    obtain ⟨h, hh⟩ := (hg1 σ.val σ.2).2
    exact hh

end ConantTerry.Orders
end

theorem solution : type_of% @ConantTerry.Orders.chk_tree_ramsey := @ConantTerry.Orders.chk_tree_ramsey
