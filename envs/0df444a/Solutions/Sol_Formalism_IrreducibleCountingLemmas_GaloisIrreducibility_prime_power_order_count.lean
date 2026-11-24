-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_power_order_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:51:01.800563+00:00
-- url     : https://prove2.me/submissions/5c7997d8-08a3-46e9-8a03-d94381829468

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ProdPowFactorizationLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
private theorem sum_le_prod_of_two_le (s : Finset ℕ) (f : ℕ → ℕ) (h : ∀ l ∈ s, 2 ≤ f l) :
    ∑ l ∈ s, f l ≤ ∏ l ∈ s, f l ∧ (s = ∅ ∨ 2 ≤ ∏ l ∈ s, f l) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h' : ∀ l ∈ s, 2 ≤ f l := fun l hl => h l (Finset.mem_insert_of_mem hl)
    obtain ⟨ih1, ih2⟩ := ih h'
    have hfa := h a (Finset.mem_insert_self a s)
    have hpos : 0 < ∏ l ∈ s, f l := Finset.prod_pos (fun l hl => by have := h' l hl; omega)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, Or.inr (by nlinarith)⟩
    rcases ih2 with rfl | h2
    · simp
    · nlinarith
private theorem prod_pow_factorization_le (s : Finset ℕ) (n : ℕ) (hn : n ≠ 0) (hs : ∀ l ∈ s, l.Prime) :
    ∏ l ∈ s, l ^ n.factorization l ≤ n := by
  classical
  calc ∏ l ∈ s, l ^ n.factorization l ≤ ∏ l ∈ s ∪ n.primeFactors, l ^ n.factorization l := by
        apply Finset.prod_le_prod_of_subset_of_one_le' Finset.subset_union_left
        intro l hl _
        rcases Finset.mem_union.1 hl with h | h
        · exact Nat.one_le_pow _ _ (hs l h).pos
        · exact Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors h).pos
    _ = ∏ l ∈ n.primeFactors, l ^ n.factorization l := by
        symm
        apply Finset.prod_subset Finset.subset_union_right
        intro l _ hl
        have : n.factorization l = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hl
        rw [this, pow_zero]
    _ = n := by
        conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
        rfl
private theorem lte_val (g δ l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hδ : 1 ≤ δ) (hl : l.Prime)
    (hd : l ∣ g - 1) : padicValNat l (g ^ δ - 1) = padicValNat l (g - 1) + padicValNat l δ := by
  have : Fact l.Prime := ⟨hl⟩
  have hlg : ¬ l ∣ g := by
    intro h
    have : l ∣ 1 := by
      have h2 : l ∣ g - (g - 1) := Nat.dvd_sub h hd
      have : g - (g - 1) = 1 := by omega
      rwa [this] at h2
    exact hl.one_lt.ne' (Nat.dvd_one.1 this)
  rcases hl.eq_two_or_odd' with rfl | hodd
  · have hgz : (4 : ℤ) ∣ (g : ℤ) - 1 := by
      have : ((g - 1 : ℕ) : ℤ) = (g : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ g)]; ring
      rw [← this]; exact_mod_cast h4
    have hg2 : ¬ (2 : ℤ) ∣ (g : ℤ) := by exact_mod_cast hlg
    have key := Int.two_pow_sub_pow' (x := (g : ℤ)) (y := 1) δ hgz hg2
    have hpos : 1 ≤ g ^ δ := Nat.one_le_pow _ _ (by omega)
    have e1 : ((g : ℤ) ^ δ - 1 ^ δ) = ((g ^ δ - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hpos]; ring
    have e2 : ((g : ℤ) - 1) = ((g - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ g)]; ring
    rw [e1, e2] at key
    have c2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
    rw [c2, Int.natCast_emultiplicity, Int.natCast_emultiplicity, Int.natCast_emultiplicity] at key
    have n1 : g ^ δ - 1 ≠ 0 := by
      have : g ^ 1 ≤ g ^ δ := Nat.pow_le_pow_right (by omega) hδ
      simp at this; omega
    rw [← padicValNat_eq_emultiplicity n1, ← padicValNat_eq_emultiplicity (by omega : g - 1 ≠ 0),
      ← padicValNat_eq_emultiplicity (by omega : δ ≠ 0)] at key
    exact_mod_cast key
  · have := padicValNat.pow_sub_pow (p := l) hodd (x := g) (y := 1) (by omega) hd hlg (n := δ) (by omega)
    simpa using this
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : PrimePowerOrderCount := by
  classical
  intro g δ hg h4 hδ
  set A := g - 1 with hA
  have hA0 : A ≠ 0 := by omega
  obtain ⟨B, hB⟩ : A ∣ g ^ δ - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 δ
  have n1 : g ^ δ - 1 ≠ 0 := by
    have : g ^ 1 ≤ g ^ δ := Nat.pow_le_pow_right (by omega) hδ
    simp at this; omega
  have hB0 : B ≠ 0 := by rintro rfl; simp at hB; exact n1 hB
  have hdiv : (g ^ δ - 1) / A = B := by rw [hB]; exact Nat.mul_div_cancel_left _ (by omega)
  rw [hdiv, ← Finset.sum_filter_add_sum_filter_not _ (fun l => l ∣ A)]
  apply add_le_add
  · have e : ∀ l ∈ (g ^ δ - 1).primeFactors.filter (fun l => l ∣ A),
        l ^ padicValNat l (g ^ δ - 1) = l ^ (δ * A).factorization l := by
      intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      rw [lte_val g δ l hg h4 hδ hp hl.2, Nat.factorization_mul (by omega) hA0,
        Finsupp.add_apply, Nat.factorization_def _ hp, Nat.factorization_def _ hp, add_comm]
    rw [Finset.sum_congr rfl e]
    refine le_trans (sum_le_prod_of_two_le _ _ ?_).1 (prod_pow_factorization_le _ _
      (Nat.mul_ne_zero (by omega) hA0) ?_)
    · intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      have : 1 ≤ (δ * A).factorization l :=
        (hp.dvd_iff_one_le_factorization (Nat.mul_ne_zero (by omega) hA0)).1 (Dvd.dvd.mul_left hl.2 _)
      calc 2 ≤ l := hp.two_le
        _ = l ^ 1 := (pow_one l).symm
        _ ≤ _ := Nat.pow_le_pow_right hp.pos this
    · intro l hl
      exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hl).1
  · have e : ∀ l ∈ (g ^ δ - 1).primeFactors.filter (fun l => ¬ l ∣ A),
        l ^ padicValNat l (g ^ δ - 1) = l ^ B.factorization l := by
      intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      rw [← Nat.factorization_def _ hp, hB, Nat.factorization_mul hA0 hB0]
      have : A.factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hl.2
      simp [this]
    rw [Finset.sum_congr rfl e]
    refine le_trans (sum_le_prod_of_two_le _ _ ?_).1 (prod_pow_factorization_le _ _ hB0 ?_)
    · intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      have hd : l ∣ B := by
        have := Nat.dvd_of_mem_primeFactors hl.1
        rw [hB] at this
        exact (hp.dvd_mul.1 this).resolve_left hl.2
      have : 1 ≤ B.factorization l := (hp.dvd_iff_one_le_factorization hB0).1 hd
      calc 2 ≤ l := hp.two_le
        _ = l ^ 1 := (pow_one l).symm
        _ ≤ _ := Nat.pow_le_pow_right hp.pos this
    · intro l hl
      exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hl).1
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
