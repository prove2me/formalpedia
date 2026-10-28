-- Prove2me | solution 1 for Erdos624.odd_layer_label_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:51.99054+00:00
-- url     : https://prove2.me/submissions/c2a7e7bb-6485-4d75-914e-b19303cdbd41

import Mathlib
open Finset

namespace E624R14O
open Finset Module

lemma indep_sum_ne {ι M : Type*} [DecidableEq ι] [AddCommGroup M] [Module (ZMod 2) M]
    (v : ι → M) (s : Set ι) (hv : LinearIndepOn (ZMod 2) v s) (F : Finset ι)
    (hF : (F : Set ι) ⊆ s) (hne : F.Nonempty) : ∑ x ∈ F, v x ≠ 0 := by
  intro hsum
  obtain ⟨y, hy⟩ := hne
  have hrest : ∑ x ∈ F.erase y, v x ∈ Submodule.span (ZMod 2) (v '' (s \ {y})) := by
    apply Submodule.sum_mem
    intro x hx
    rw [mem_erase] at hx
    exact Submodule.subset_span ⟨x, ⟨hF hx.2, by simpa using hx.1⟩, rfl⟩
  have hpy : v y = -(∑ x ∈ F.erase y, v x) := by
    rw [← add_sum_erase F v hy] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  exact hv.notMem_span (hF hy) (hpy ▸ Submodule.neg_mem _ hrest)

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

lemma half_count (r : ℕ) (v : Fin r → ZMod 2) (hv : v ≠ 0) :
    2 * #((univ : Finset (Fin r → ZMod 2)).filter (fun w => w ⬝ᵥ v = 1)) = 2 ^ r := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  have hvi : v i = 1 := (zmod2_cases (v i)).resolve_left hi
  have hshift : ∀ w : Fin r → ZMod 2, (w + Pi.single i 1) ⬝ᵥ v = w ⬝ᵥ v + 1 := by
    intro w; rw [add_dotProduct, single_dotProduct, one_mul, hvi]
  have heq : #((univ : Finset (Fin r → ZMod 2)).filter (fun w => w ⬝ᵥ v = 1)) =
      #((univ : Finset (Fin r → ZMod 2)).filter (fun w => ¬ w ⬝ᵥ v = 1)) := by
    refine card_nbij' (fun w => w + Pi.single i 1) (fun w => w + Pi.single i 1) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
      rw [hshift, hw]; decide
    · intro w hw
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
      rw [hshift]
      rcases zmod2_cases (w ⬝ᵥ v) with h | h
      · rw [h]; decide
      · exact absurd h hw
    · intro w _; simp only; rw [add_assoc, ← Pi.single_add]
      have : (1 : ZMod 2) + 1 = 0 := by decide
      rw [this, Pi.single_zero, add_zero]
    · intro w _; simp only; rw [add_assoc, ← Pi.single_add]
      have : (1 : ZMod 2) + 1 = 0 := by decide
      rw [this, Pi.single_zero, add_zero]
  have htot := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin r → ZMod 2))) (fun w => w ⬝ᵥ v = 1)
  rw [card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at htot
  omega

theorem odd_layer {U : Type*} [Fintype U] [DecidableEq U] (r k j : ℕ) (hj : Odd j)
    (hjk : j ≤ k) (q : U → (Fin r → ZMod 2)) (P : Finset U)
    (hcov : ∀ Y ⊆ P, #Y = k → ∃ A ⊆ Y, #A = j ∧ ∑ x ∈ A, q x = 0) :
    #(P.filter (fun x => q x ≠ 0)) ≤ 2 * (k - 1) ∧
    (2 * k + j - 3 ≤ #P →
      finrank (ZMod 2) (Submodule.span (ZMod 2) (q '' (P : Set U))) + j ≤ k) := by
  classical
  have hj1 : 1 ≤ j := hj.pos
  -- one-sets are small
  have hone : ∀ w : Fin r → ZMod 2, #(P.filter (fun x => w ⬝ᵥ q x = 1)) ≤ k - 1 := by
    intro w
    by_contra hc
    obtain ⟨Y, hY, hYc⟩ := exists_subset_card_eq (s := P.filter (fun x => w ⬝ᵥ q x = 1))
      (n := k) (by omega)
    obtain ⟨A, hAY, hAc, hA0⟩ := hcov Y (hY.trans (filter_subset _ _)) hYc
    have h1 : w ⬝ᵥ ∑ x ∈ A, q x = ∑ x ∈ A, (1 : ZMod 2) := by
      rw [dotProduct_sum]
      exact sum_congr rfl fun x hx => (mem_filter.1 (hY (hAY hx))).2
    rw [hA0, dotProduct_zero, sum_const, hAc, nsmul_eq_mul, mul_one] at h1
    obtain ⟨t, rfl⟩ := hj
    have : ((2 * t + 1 : ℕ) : ZMod 2) = 1 := by
      push_cast; rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
    rw [this] at h1; exact absurd h1 (by decide)
  have hsum : ∑ w : Fin r → ZMod 2, #(P.filter (fun x => w ⬝ᵥ q x = 1)) =
      ∑ x ∈ P, #((univ : Finset (Fin r → ZMod 2)).filter (fun w => w ⬝ᵥ q x = 1)) := by
    simp only [card_filter]; exact sum_comm
  have hpart1 : #(P.filter (fun x => q x ≠ 0)) ≤ 2 * (k - 1) := by
    have hle : ∑ w : Fin r → ZMod 2, #(P.filter (fun x => w ⬝ᵥ q x = 1)) ≤ 2 ^ r * (k - 1) := by
      calc _ ≤ ∑ _w : Fin r → ZMod 2, (k - 1) := sum_le_sum fun w _ => hone w
        _ = 2 ^ r * (k - 1) := by
          rw [sum_const, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, smul_eq_mul]
    have hge : #(P.filter (fun x => q x ≠ 0)) * 2 ^ r ≤
        2 * ∑ x ∈ P, #((univ : Finset (Fin r → ZMod 2)).filter (fun w => w ⬝ᵥ q x = 1)) := by
      rw [mul_sum]
      calc #(P.filter (fun x => q x ≠ 0)) * 2 ^ r
          = ∑ x ∈ P.filter (fun x => q x ≠ 0),
              2 * #((univ : Finset (Fin r → ZMod 2)).filter (fun w => w ⬝ᵥ q x = 1)) := by
            rw [sum_congr rfl fun x hx => half_count r (q x) (mem_filter.1 hx).2, sum_const,
              smul_eq_mul]
        _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
    rw [← hsum] at hge
    have : #(P.filter (fun x => q x ≠ 0)) * 2 ^ r ≤ 2 * (k - 1) * 2 ^ r := by nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  refine ⟨hpart1, fun hP => ?_⟩
  by_contra hc
  push Not at hc
  -- extract an independent subset of the labels
  obtain ⟨s, hsP, -, hPs, hsind⟩ := exists_linearIndepOn_extension (K := ZMod 2) (v := q)
    (s := ∅) (t := (P : Set U)) (linearIndepOn_empty _ _) (Set.empty_subset _)
  have hspan : Submodule.span (ZMod 2) (q '' s) = Submodule.span (ZMod 2) (q '' (P : Set U)) := by
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono hsP)
    · rw [Submodule.span_le]; exact hPs
  have hcs := linearIndependent_iff_card_eq_finrank_span.1 hsind
  rw [Set.finrank, ← Set.image_eq_range, hspan] at hcs
  set S := s.toFinset with hS
  have hScard : #S = finrank (ZMod 2) (Submodule.span (ZMod 2) (q '' (P : Set U))) := by
    rw [hS, Set.toFinset_card, hcs]
  obtain ⟨I, hIS, hIc⟩ := exists_subset_card_eq (s := S) (n := k - j + 1) (by omega)
  have hIs : (I : Set U) ⊆ s := fun x hx => by
    have := hIS hx; rw [hS, Set.mem_toFinset] at this; exact this
  have hIP : I ⊆ P := fun x hx => by exact_mod_cast hsP (hIs hx)
  have hIind : LinearIndepOn (ZMod 2) q (I : Set U) := hsind.mono hIs
  -- zero labels
  have hz : j - 1 ≤ #(P.filter (fun x => q x = 0)) := by
    have := card_filter_add_card_filter_not (s := P) (fun x => q x = 0)
    simp only [ne_eq] at hpart1
    omega
  obtain ⟨Z1, hZ1, hZ1c⟩ := exists_subset_card_eq hz
  have hdisj : Disjoint I Z1 := by
    rw [disjoint_left]
    intro x hxI hxZ
    have h0 := (mem_filter.1 (hZ1 hxZ)).2
    exact hIind.ne_zero (by exact_mod_cast hxI) h0
  obtain ⟨A, hAY, hAc, hA0⟩ := hcov (I ∪ Z1) (union_subset hIP (hZ1.trans (filter_subset _ _)))
    (by rw [card_union_of_disjoint hdisj]; omega)
  set F := A.filter (fun x => x ∈ I) with hF
  have hsplit : ∑ x ∈ A, q x = ∑ x ∈ F, q x := by
    rw [hF, sum_filter]
    refine sum_congr rfl fun x hx => ?_
    split_ifs with h
    · rfl
    · have := hAY hx
      rw [mem_union] at this
      rcases this with h' | h'
      · exact absurd h' h
      · exact (mem_filter.1 (hZ1 h')).2
  have hFne : F.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have : A ⊆ Z1 := by
      intro x hx
      have := hAY hx
      rw [mem_union] at this
      rcases this with h' | h'
      · have : x ∈ F := mem_filter.2 ⟨hx, h'⟩
        rw [hne] at this; simp at this
      · exact h'
    have := card_le_card this
    omega
  exact indep_sum_ne q (I : Set U) hIind F (fun x hx => by
    have := (mem_filter.1 hx).2; exact_mod_cast this) hFne (hsplit ▸ hA0)
end E624R14O

namespace Erdos624

theorem odd_layer_label_rank_bound {U : Type*} [Fintype U] [DecidableEq U] (r k j : ℕ) (hj : Odd j)
    (hjk : j ≤ k) (q : U → (Fin r → ZMod 2)) (P : Finset U)
    (hcov : ∀ Y ⊆ P, #Y = k → ∃ A ⊆ Y, #A = j ∧ ∑ x ∈ A, q x = 0) :
    #(P.filter (fun x => q x ≠ 0)) ≤ 2 * (k - 1) ∧
    (2 * k + j - 3 ≤ #P →
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (q '' (P : Set U))) + j ≤ k) := by
  exact E624R14O.odd_layer r k j hj hjk q P hcov

end Erdos624

open Finset

theorem solution {U : Type*} [Fintype U] [DecidableEq U] (r k j : ℕ) (hj : Odd j)
    (hjk : j ≤ k) (q : U → (Fin r → ZMod 2)) (P : Finset U)
    (hcov : ∀ Y ⊆ P, #Y = k → ∃ A ⊆ Y, #A = j ∧ ∑ x ∈ A, q x = 0) :
    #(P.filter (fun x => q x ≠ 0)) ≤ 2 * (k - 1) ∧
    (2 * k + j - 3 ≤ #P →
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (q '' (P : Set U))) + j ≤ k) :=
  Erdos624.odd_layer_label_rank_bound r k j hj hjk q P hcov
