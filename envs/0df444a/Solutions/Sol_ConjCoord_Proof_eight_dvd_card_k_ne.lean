-- Prove2me | solution 1 for ConjCoord.Proof.eight_dvd_card_k_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:59.830632+00:00
-- url     : https://prove2.me/submissions/e655adbf-f94c-46fe-8eb4-472179d6a67e

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares
public import Theorems.Thm_ConjCoord_Proof_sq_mod16_ne5
public import Theorems.Thm_ConjCoord_Proof_mem_gset
public import Theorems.Thm_ConjCoord_Proof_neg_cond
public import Theorems.Thm_ConjCoord_Proof_card_eq_two_mul_filter


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {m : ℕ} :
    8 ∣ ((gset m).filter fun v => ¬ v.2.2 = 0).card := by
  set S1 := (gset m).filter fun v => ¬ v.2.2 = 0
  have hS1 : ∀ v ∈ S1, v ∈ gset m ∧ ¬ v.2.2 = 0 := fun v hv => mem_filter.mp hv
  rw [card_eq_two_mul_filter S1 (fun v => (v.1, v.2.1, -v.2.2)) (fun v => 0 < v.2.2) ?_ ?_ ?_]
  · set S2 := S1.filter fun v => 0 < v.2.2
    have hS2 : ∀ v ∈ S2, v ∈ gset m ∧ 0 < v.2.2 := fun v hv =>
      ⟨(hS1 v (mem_filter.mp hv).1).1, (mem_filter.mp hv).2⟩
    rw [card_eq_two_mul_filter S2 (fun v => (-v.1, v.2.1, v.2.2)) (fun v => 0 < v.1) ?_ ?_ ?_]
    · set S3 := S2.filter fun v => 0 < v.1
      have hS3 : ∀ v ∈ S3, v ∈ gset m ∧ 0 < v.2.2 ∧ 0 < v.1 := fun v hv =>
        ⟨(hS2 v (mem_filter.mp hv).1).1, (hS2 v (mem_filter.mp hv).1).2, (mem_filter.mp hv).2⟩
      rw [card_eq_two_mul_filter S3 (fun v => (v.1, -v.2.1, v.2.2)) (fun v => 0 < v.2.1) ?_ ?_ ?_]
      · exact ⟨_, by ring⟩
      · intro v hv
        obtain ⟨hg, hk, ha⟩ := hS3 v hv
        rw [mem_gset] at hg
        simp only [S3, S2, S1, mem_filter, mem_gset, neg_sq, neg_cond]
        exact ⟨⟨⟨hg, by omega⟩, hk⟩, ha⟩
      · intro v _; simp
      · intro v hv
        obtain ⟨hg, -, -⟩ := hS3 v hv
        rw [mem_gset] at hg
        have : v.2.1 ≠ 0 := by rintro h; rw [h] at hg; omega
        simp only; constructor <;> intro h <;> omega
    · intro v hv
      obtain ⟨hg, hk⟩ := hS2 v hv
      rw [mem_gset] at hg
      simp only [S2, S1, mem_filter, mem_gset, neg_sq]
      exact ⟨⟨hg, by omega⟩, hk⟩
    · intro v _; simp
    · intro v hv
      obtain ⟨hg, -⟩ := hS2 v hv
      rw [mem_gset] at hg
      have : v.1 ≠ 0 := by
        rintro h; rw [h] at hg; have := sq_mod16_ne5 v.2.1; simp at hg; omega
      simp only; constructor <;> intro h <;> omega
  · intro v hv
    obtain ⟨hg, hk⟩ := hS1 v hv
    rw [mem_gset] at hg
    simp only [S1, mem_filter, mem_gset, neg_sq]
    exact ⟨hg, by omega⟩
  · intro v _; simp
  · intro v hv
    obtain ⟨-, hk⟩ := hS1 v hv
    simp only; constructor <;> intro h <;> omega
end ConjCoord.Proof
