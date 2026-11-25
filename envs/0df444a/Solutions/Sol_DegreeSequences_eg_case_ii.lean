-- Prove2me | solution 1 for DegreeSequences.eg_case_ii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:07:08.491185+00:00
-- url     : https://prove2.me/submissions/1e82ec8f-abce-4e2a-accb-7fbc8ac45acd

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {n : ℕ} (d : Fin n → ℕ) (hEG : ∀ k ≤ n, ∑ i with i.val < k, d i ≤
      k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k)
    (t p : Fin n) (htp : t < p) (k : ℕ) (hkt : k ≤ t.val) (hLk : ∑ i with i.val < k, d i = k * d t)
    (htop : ∀ i ≤ t, d i = d t) (hp1 : 1 ≤ d p) (h1 : k < d t) (h2 : d p ≤ k) :
    ∑ i with i.val < k, d i + 1 ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k := by
  have htp' : t.val < p.val := htp
  have hkn : k < n := by have := p.isLt; omega
  set kk : Fin n := ⟨k, hkn⟩ with hkk
  have hdkk : d kk = d t := htop kk (by rw [Fin.le_iff_val_le_val]; exact hkt)
  have hL1 : ∑ i with i.val < k + 1, d i = ∑ i with i.val < k, d i + d t := by
    have : (univ.filter fun i : Fin n => i.val < k + 1) =
        insert kk (univ.filter fun i : Fin n => i.val < k) := by
      ext i; simp [hkk, Fin.ext_iff]; omega
    rw [this, sum_insert (by simp [hkk]), hdkk, add_comm]
  set N := ∑ i with k + 1 ≤ i.val, min (d i) k with hN
  set c := ∑ i with k + 1 ≤ i.val, (if k + 1 ≤ d i then 1 else 0) with hc
  have hM0 : ∑ i with k ≤ i.val, min (d i) k = k + N := by
    have : (univ.filter fun i : Fin n => k ≤ i.val) =
        insert kk (univ.filter fun i : Fin n => k + 1 ≤ i.val) := by
      ext i; simp [hkk, Fin.ext_iff]; omega
    rw [this, sum_insert (by simp [hkk]), hdkk, min_eq_right h1.le]
  have hM1 : ∑ i with k + 1 ≤ i.val, min (d i) (k + 1) = N + c := by
    rw [hN, hc, ← sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> omega
  have hNc : k * c + 1 ≤ N := by
    have hpmem : p ∈ (univ.filter fun i : Fin n => k + 1 ≤ i.val) := by simp; omega
    calc k * c + 1 = ∑ i with k + 1 ≤ i.val,
          (k * (if k + 1 ≤ d i then 1 else 0) + (if i = p then 1 else 0)) := by
          rw [sum_add_distrib, ← mul_sum, sum_ite_eq']
          simp only [hpmem, ite_true, hc]
      _ ≤ N := by
          refine Finset.sum_le_sum fun i _ => ?_
          rcases eq_or_ne i p with rfl | hip
          · simp only [ite_true]; split_ifs <;> omega
          · simp only [hip, ite_false]; split_ifs <;> omega
  have hE := hEG (k + 1) hkn
  rw [hL1, hM1, Nat.add_sub_cancel] at hE
  rw [hM0]
  have hnl1 : k * (k - 1) + k = k * k := by
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  have hnl2 : (k + 1) * k = k * k + k := by ring
  have hnl3 : d t ≤ k + c → k * d t ≤ k * k + k * c := fun h => by
    have := Nat.mul_le_mul_left k h
    rw [Nat.mul_add] at this
    exact this
  rw [hLk] at hE ⊢
  rw [hnl2] at hE
  generalize k * d t = Y at *
  generalize k * (k - 1) = X at *
  generalize k * c = Z at *
  generalize k * k = W at *
  omega
end DegreeSequences
