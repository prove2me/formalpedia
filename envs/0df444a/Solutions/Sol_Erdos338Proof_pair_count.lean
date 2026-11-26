-- Prove2me | solution 1 for Erdos338Proof.pair_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:05.376945+00:00
-- url     : https://prove2.me/submissions/88d3bf52-0e53-47f9-82c8-aa3dcd5e853d

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Pairs
public import Theorems.Thm_Erdos338Proof_mem_rep
public import Theorems.Thm_Erdos338Proof_card_rep_le

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution (A : Set ℕ) (R : ℕ) {b L : ℕ} (hL : 2 * L ≤ b) :
    cnt A L * cnt A L ≤ b * cnt {m | R ≤ #(rep A m)} b + b * R + cnt A L := by
  classical
  set M : Set ℕ := {m | R ≤ #(rep A m)} with hM
  set S := (range L).filter (· ∈ A) with hS
  have hk : cnt A L = #S := rfl
  have h1 : #S.offDiag ≤ ∑ m ∈ range b, #(rep A m) := by
    rw [card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ ↦ p.1 + p.2) (t := range b)]
    · apply sum_le_sum
      intro m _
      apply card_le_card_of_injOn Prod.fst
      · intro p hp
        rw [Finset.mem_coe, mem_filter, mem_offDiag] at hp
        obtain ⟨⟨hp1, hp2, hne⟩, hsum⟩ := hp
        rw [hS, mem_filter] at hp1 hp2
        rw [Finset.mem_coe, mem_rep]
        have e : m - p.1 = p.2 := by omega
        rw [e]
        exact ⟨by omega, hp1.2, hp2.2, by omega⟩
      · intro p hp q hq hpq
        simp only [Finset.mem_coe, mem_filter] at hp hq
        exact Prod.ext hpq (by omega)
    · intro p hp
      rw [Finset.mem_coe, mem_offDiag, hS, mem_filter, mem_filter, mem_range, mem_range] at hp
      rw [Finset.mem_coe, mem_range]
      show p.1 + p.2 < b
      omega
  have h2 : ∑ m ∈ range b, #(rep A m) ≤ ∑ m ∈ range b, ((if m ∈ M then b else 0) + R) := by
    apply sum_le_sum
    intro m hm
    rw [mem_range] at hm
    split_ifs with h
    · have := card_rep_le A m
      omega
    · have h' : ¬ R ≤ #(rep A m) := h
      omega
  have h3 : ∑ m ∈ range b, ((if m ∈ M then b else 0) + R) = b * cnt M b + b * R := by
    rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, card_range, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [mul_comm]
    congr 1
    unfold cnt
    convert rfl
  have h4 := h1.trans (h2.trans h3.le)
  rw [offDiag_card] at h4
  rw [hk]
  omega
end Erdos338Proof
