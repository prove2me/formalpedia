-- Prove2me | solution 1 for DegreeSequences.eg_case_i
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:06:30.109043+00:00
-- url     : https://prove2.me/submissions/85e02417-349a-4cdf-ac39-18edc51f7fec

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {n : ℕ} (d : Fin n → ℕ) (hev : Even (∑ i, d i)) (t p : Fin n) (htp : t ≠ p)
    (hp1 : 1 ≤ d p) (k : ℕ) (hkt : k ≤ t.val) (hkp : k ≤ p.val) (hle : ∀ i, d i ≤ d t)
    (hLk : ∑ i with i.val < k, d i = k * d t) (h1 : d t ≤ k) :
    ∑ i with i.val < k, d i + 2 ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k := by
  have hMk : ∑ i with k ≤ i.val, min (d i) k = ∑ i with k ≤ i.val, d i :=
    Finset.sum_congr rfl fun i _ => min_eq_left ((hle i).trans h1)
  have htot : ∑ i with i.val < k, d i + ∑ i with k ≤ i.val, d i = ∑ i, d i := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i : Fin n => i.val < k)]
    simp only [not_lt]
  have hge : d t + d p ≤ ∑ i with k ≤ i.val, d i := by
    rw [← sum_pair htp]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [hkt, hkp]
  have hnl : k * d t ≤ k * (k - 1) + d t := by
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]
      have := Nat.mul_le_mul_left k h1
      rw [Nat.succ_mul]
      nlinarith
  obtain ⟨u, hu⟩ := Nat.even_mul_pred_self k
  obtain ⟨v, hv⟩ := hev
  rw [hMk, hLk]
  rw [hLk] at htot
  generalize k * d t = Y at *
  generalize k * (k - 1) = X at *
  omega
end DegreeSequences
