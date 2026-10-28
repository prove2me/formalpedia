-- Prove2me | solution 1 for Erdos624.greedy_matching_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:14:25.44632+00:00
-- url     : https://prove2.me/submissions/823150d6-0ae3-4c42-aba4-6472d5e31345

import Mathlib
open Finset
namespace E624R16M
open Finset

/-- If `s < k * m` and `k ≥ 1`, then `⌊s/k⌋ + 1 ≤ m`. -/
lemma nat_lt_mul_div {k s m : ℕ} (hk : 0 < k) (h : s < k * m) : s / k + 1 ≤ m := by
  rw [Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul hk, mul_comm]
  exact h

/-- Maximal pairwise-disjoint subfamily: its union is a transversal. -/
lemma maximal_matching_is_transversal {α : Type*} [DecidableEq α]
    (F M : Finset (Finset α))
    (hMsub : M ⊆ F)
    (hMpair : (M : Set (Finset α)).PairwiseDisjoint id)
    (hne : ∀ A ∈ F, A.Nonempty)
    (hmax : ∀ M' ⊆ F, (M' : Set (Finset α)).PairwiseDisjoint id → #M' ≤ #M) :
    ∀ A ∈ F, (A ∩ M.biUnion id).Nonempty := by
  intro A hA
  by_contra hempty
  have hAdis : ∀ B ∈ M, Disjoint A B := by
    intro B hB
    rw [disjoint_iff_inter_eq_empty]
    apply eq_empty_of_forall_notMem
    intro x hx
    have : x ∈ A ∩ M.biUnion id := by
      rw [mem_inter] at hx ⊢
      exact ⟨hx.1, mem_biUnion.2 ⟨B, hB, hx.2⟩⟩
    exact hempty ⟨x, this⟩
  have hAnotin : A ∉ M := by
    intro hAM
    have : (A ∩ M.biUnion id).Nonempty := by
      obtain ⟨x, hx⟩ := hne A hA
      exact ⟨x, mem_inter.2 ⟨hx, mem_biUnion.2 ⟨A, hAM, hx⟩⟩⟩
    exact hempty this
  set M' := insert A M
  have hM'sub : M' ⊆ F := insert_subset hA hMsub
  have hM'pair : (M' : Set (Finset α)).PairwiseDisjoint id := by
    rw [show (M' : Set (Finset α)) = insert A (M : Set (Finset α)) from coe_insert A M]
    exact hMpair.insert (fun B hB _ => hAdis B hB)
  have hcard : #M' = #M + 1 := card_insert_of_notMem hAnotin
  have : #M' ≤ #M := hmax M' hM'sub hM'pair
  omega

/-- (MATCH) core: a family of nonempty sets of size ≤ `k` with transversal number > `s`
has matching number ≥ `⌊s/k⌋ + 1`. -/
theorem match_bound {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (k s : ℕ) (hk : 1 ≤ k)
    (hne : ∀ A ∈ F, A.Nonempty)
    (hsize : ∀ A ∈ F, #A ≤ k)
    (hτ : ∀ T : Finset α, (∀ A ∈ F, (A ∩ T).Nonempty) → s < #T) :
    ∃ M ⊆ F, (M : Set (Finset α)).PairwiseDisjoint id ∧ s / k + 1 ≤ #M := by
  classical
  let S : Finset (Finset (Finset α)) :=
    F.powerset.filter (fun M : Finset (Finset α) => (M : Set (Finset α)).PairwiseDisjoint id)
  have h0 : (∅ : Finset (Finset α)) ∈ S := by
    refine mem_filter.2 ⟨mem_powerset.2 (empty_subset _), ?_⟩
    intro a ha; exact (notMem_empty a ha).elim
  obtain ⟨M, hMmem, hmax⟩ := exists_max_image S (fun M => #M) ⟨∅, h0⟩
  have hMpair : (M : Set (Finset α)).PairwiseDisjoint id := (mem_filter.1 hMmem).2
  have hMsub : M ⊆ F := mem_powerset.1 (mem_filter.1 hMmem).1
  refine ⟨M, hMsub, hMpair, ?_⟩
  have hmax' : ∀ M' ⊆ F, (M' : Set (Finset α)).PairwiseDisjoint id → #M' ≤ #M := by
    intro M' hsub hpair
    have hM'S : M' ∈ S := mem_filter.2 ⟨mem_powerset.2 hsub, hpair⟩
    exact hmax M' hM'S
  have htrav := maximal_matching_is_transversal F M hMsub hMpair hne hmax'
  have hs : s < #(M.biUnion id) := hτ (M.biUnion id) htrav
  have hle : #(M.biUnion id) ≤ k * #M := by
    calc #(M.biUnion id)
        ≤ ∑ A ∈ M, #A := card_biUnion_le
      _ ≤ ∑ _A ∈ M, k := sum_le_sum fun A hA => hsize A (hMsub hA)
      _ = k * #M := by rw [sum_const, smul_eq_mul, mul_comm]
  exact nat_lt_mul_div (Nat.pos_of_ne_zero (by omega)) (lt_of_lt_of_le hs hle)

end E624R16M

namespace Erdos624

theorem greedy_matching_lower_bound {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (k s : ℕ) (hk : 1 ≤ k)
    (hne : ∀ A ∈ F, A.Nonempty)
    (hsize : ∀ A ∈ F, #A ≤ k)
    (hτ : ∀ T : Finset α, (∀ A ∈ F, (A ∩ T).Nonempty) → s < #T) :
    ∃ M ⊆ F, (M : Set (Finset α)).PairwiseDisjoint id ∧ s / k + 1 ≤ #M := by
  exact E624R16M.match_bound F k s hk hne hsize hτ

end Erdos624

open Finset

theorem solution {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (k s : ℕ) (hk : 1 ≤ k)
    (hne : ∀ A ∈ F, A.Nonempty)
    (hsize : ∀ A ∈ F, #A ≤ k)
    (hτ : ∀ T : Finset α, (∀ A ∈ F, (A ∩ T).Nonempty) → s < #T) :
    ∃ M ⊆ F, (M : Set (Finset α)).PairwiseDisjoint id ∧ s / k + 1 ≤ #M :=
  Erdos624.greedy_matching_lower_bound F k s hk hne hsize hτ
