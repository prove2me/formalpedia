-- Prove2me | solution 1 for DegreeSequences.egReduce_EG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:17:55.338435+00:00
-- url     : https://prove2.me/submissions/a67e2d3b-d1db-43b5-98d0-1aaa0985ad60

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_egReduce_sum_lt
public import Theorems.Thm_DegreeSequences_egReduce_sum_min
public import Theorems.Thm_DegreeSequences_eg_case_i
public import Theorems.Thm_DegreeSequences_eg_case_ii

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {n : ℕ} (d : Fin n → ℕ) (hd : Antitone d) (hev : Even (∑ i, d i))
    (hEG : ∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k)
    (t p : Fin n) (htp : t < p) (hp1 : 1 ≤ d p) (htop : ∀ i ≤ t, d i = d t) :
    ∀ k ≤ n, ∑ i with i.val < k, egReduce d t p i ≤
      k * (k - 1) + ∑ i with k ≤ i.val, min (egReduce d t p i) k := by
  intro k hk
  have htp' : t ≠ p := htp.ne
  have htpv : t.val < p.val := htp
  have ht1 : 1 ≤ d t := le_trans hp1 (hd htp.le)
  have hL := egReduce_sum_lt d t p htp' ht1 hp1 (univ.filter fun i : Fin n => i.val < k)
  have hM := egReduce_sum_min d t p htp' ht1 hp1 k (univ.filter fun i : Fin n => k ≤ i.val)
  simp only [mem_filter, mem_univ, true_and] at hL hM
  have hE := hEG k hk
  by_cases hkt : k ≤ t.val
  · have hle : ∀ i, d i ≤ d t := fun i => by
      rcases le_total i t with h | h
      · exact (htop i h).le
      · exact hd h
    have hLk : ∑ i with i.val < k, d i = k * d t := by
      have : ∀ i ∈ univ.filter (fun i : Fin n => i.val < k), d i = d t := fun i hi =>
        htop i (by rw [mem_filter] at hi; rw [Fin.le_iff_val_le_val]; omega)
      rw [sum_congr rfl this, sum_const, smul_eq_mul, Fin.card_filter_val_lt, min_eq_right hk]
    by_cases h1 : d t ≤ k
    · have := eg_case_i d hev t p htp' hp1 k hkt (by omega) hle hLk h1
      split_ifs at hL hM <;> omega
    · by_cases h2 : d p ≤ k
      · have := eg_case_ii d hEG t p htp k hkt hLk htop hp1 (by omega) h2
        split_ifs at hL hM <;> omega
      · split_ifs at hL hM <;> omega
  · split_ifs at hL hM <;> omega
end DegreeSequences
