-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.blockDimensionIdentities
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:52:57.33139+00:00
-- url     : https://prove2.me/submissions/ac7e0b0f-de7b-408f-877b-7ad24c5707e1

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_two_mul_card_lt_pairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.LogVandermondeBounds.StandardLattice
open Finset
private lemma card_ordered_pairs_in_shifted_interval (a n N : ℕ) (h : a + n ≤ N) :
    ((range N ×ˢ range N).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ a ≤ p.1 ∧ p.2 < a + n)).card =
      ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
  refine Finset.card_nbij' (fun p => (p.1 - a, p.2 - a)) (fun p => (p.1 + a, p.2 + a)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range] at hp
    ext <;> simp <;> omega
  · intro p hp
    ext <;> simp
end Formalism.LogVandermondeBounds.StandardLattice
end

set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution : BlockDimensionIdentities := by
  intro k m rS r hm hme hrS hr blockOf dimN
  have hm2 : m = 2 * rS + 2 := by obtain ⟨t, ht⟩ := hme; omega
  have hsame : ∀ i j, i < j → j < r → (blockOf i = blockOf j ↔ rS ≤ i ∧ j < rS + (k + 1)) := by
    intro i j hij hj
    simp only [blockOf]
    split_ifs <;> omega
  have hA := two_mul_card_lt_pairs r
  have hB := card_ordered_pairs_in_shifted_interval rS (k + 1) r (by omega)
  have hC := two_mul_card_lt_pairs (k + 1)
  simp only [Nat.add_sub_cancel] at hC
  have hsplit : (((range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2)).filter
      (fun p : ℕ × ℕ => blockOf p.1 = blockOf p.2)).card +
      (((range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2)).filter
      (fun p : ℕ × ℕ => ¬ blockOf p.1 = blockOf p.2)).card =
      ((range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
    first
      | exact Finset.filter_card_add_filter_neg_card_eq_card _
      | exact Finset.card_filter_add_card_filter_not _
      | exact Finset.card_filter_add_card_filter_neg _
      | (rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _),
          Finset.filter_union_filter_neg_eq])
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have e1 : (range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ blockOf p.1 = blockOf p.2) =
      (range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ rS ≤ p.1 ∧ p.2 < rS + (k + 1)) := by
    apply Finset.filter_congr
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hsame _ _ h1 hp.2).1 h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hsame _ _ h1 hp.2).2 h2⟩
  have e2 : dimN = ((range r ×ˢ range r).filter
      (fun p : ℕ × ℕ => p.1 < p.2 ∧ ¬ blockOf p.1 = blockOf p.2)).card := rfl
  rw [e1, hB, ← e2] at hsplit
  have hdim : 2 * dimN + (k + 1) * k = r * (r - 1) := by omega
  have hdZ : 2 * (dimN : ℤ) = (r : ℤ) * ((r : ℤ) - 1) - ((k : ℤ) + 1) * k := by
    have := congrArg (Nat.cast : ℕ → ℤ) hdim
    push_cast [Nat.cast_sub (show 1 ≤ r by omega)] at this
    linarith
  have hrZ : (r : ℤ) = k + 1 + 2 * rS := by exact_mod_cast hr
  have hmZ : (m : ℤ) = 2 * rS + 2 := by exact_mod_cast hm2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hrZ, hmZ]; ring
  · linear_combination hdZ - hrZ
  · linear_combination -hdZ + hrZ
  · ring
  · rw [hrZ, hmZ]; ring
end Formalism.LogVandermondeBounds.StandardLattice
