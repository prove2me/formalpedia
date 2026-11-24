-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.cycle_type_probability
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:52.539435+00:00
-- url     : https://prove2.me/submissions/e0f9770b-858c-4358-b1c1-c868c19476d1

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
private theorem typeMultiset_count (s : Finset ℕ) (n : ℕ → ℕ) (a : ℕ) :
    (typeMultiset s n).count a = if a ∈ s then n a else 0 := by
  classical
  unfold typeMultiset
  rw [Multiset.count_sum']
  simp [Multiset.count_replicate]
private theorem typeMultiset_sum (s : Finset ℕ) (n : ℕ → ℕ) :
    (typeMultiset s n).sum = ∑ d ∈ s, d * n d := by
  classical
  unfold typeMultiset
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.sum_add, ih, Multiset.sum_replicate,
      smul_eq_mul, mul_comm]
private theorem typeMultiset_prod (s : Finset ℕ) (n : ℕ → ℕ) :
    (typeMultiset s n).prod = ∏ d ∈ s, d ^ n d := by
  classical
  unfold typeMultiset
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Multiset.prod_add, ih, Multiset.prod_replicate]
private theorem typeMultiset_fact (s : Finset ℕ) (n : ℕ → ℕ) :
    ∏ a ∈ (typeMultiset s n).toFinset, ((typeMultiset s n).count a).factorial =
      ∏ d ∈ s, (n d).factorial := by
  classical
  rw [Finset.prod_subset (s₁ := (typeMultiset s n).toFinset) (s₂ := s) ?_ ?_]
  · refine Finset.prod_congr rfl fun d hd => ?_
    rw [typeMultiset_count, if_pos hd]
  · intro a ha
    rw [Multiset.mem_toFinset, ← Multiset.count_pos, typeMultiset_count] at ha
    by_contra h
    rw [if_neg h] at ha
    exact lt_irrefl 0 ha
  · intro a _ ha
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at ha
    rw [ha, Nat.factorial_zero]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : CycleTypeProb := by
  unfold CycleTypeProb
  intro N n hN
  classical
  have hsumle : (typeMultiset (Finset.Icc 2 N) n).sum ≤ N := by
    rw [typeMultiset_sum]
    exact le_trans (Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_left (by norm_num : 1 ≤ 2))) hN.le
  have htwo : ∀ a ∈ typeMultiset (Finset.Icc 2 N) n, 2 ≤ a := by
    intro a ha
    rw [← Multiset.count_pos, typeMultiset_count] at ha
    split_ifs at ha with h
    · exact (Finset.mem_Icc.1 h).1
    · exact absurd ha (lt_irrefl 0)
  have key := Equiv.Perm.card_of_cycleType_mul_eq (Fin N) (typeMultiset (Finset.Icc 2 N) n)
  rw [if_pos ⟨by simpa using hsumle, htwo⟩, Fintype.card_fin, typeMultiset_prod, typeMultiset_fact] at key
  have hprod : ∏ d ∈ Finset.Icc 1 N, (d ^ n d * (n d).factorial) =
      (N - (typeMultiset (Finset.Icc 2 N) n).sum).factorial * (∏ d ∈ Finset.Icc 2 N, d ^ n d) *
        ∏ d ∈ Finset.Icc 2 N, (n d).factorial := by
    rw [typeMultiset_sum]
    rcases Nat.eq_zero_or_pos N with rfl | hN1
    · simp
    · have hI : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := (Finset.insert_Icc_add_one_left_eq_Icc hN1).symm
      rw [hI, Finset.prod_insert (by simp)]
      rw [hI, Finset.sum_insert (by simp)] at hN
      have h1 : N - ∑ d ∈ Finset.Icc 2 N, d * n d = n 1 := by omega
      rw [h1, one_pow, one_mul, Finset.prod_mul_distrib]
      ring
  rw [hprod]
  convert key using 3
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    ext a
    rw [typeMultiset_count]
    split_ifs with ha
    · exact h a ha
    · rw [Multiset.count_eq_zero]
      intro hmem
      apply ha
      rw [Finset.mem_Icc]
      refine ⟨Equiv.Perm.two_le_of_mem_cycleType hmem, ?_⟩
      calc a ≤ σ.support.card := Equiv.Perm.le_card_support_of_mem_cycleType hmem
        _ ≤ Fintype.card (Fin N) := Finset.card_le_univ _
        _ = N := Fintype.card_fin N
  · intro h d hd
    rw [h, typeMultiset_count, if_pos hd]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
