-- Prove2me | solution 1 for ConjCoord.Proof.gCount_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:39.477028+00:00
-- url     : https://prove2.me/submissions/b7fa5b40-82e5-41cd-b0c8-4e1ab3cecfa0

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares
public import Theorems.Thm_ConjCoord_Proof_sq_mod16_ne5
public import Theorems.Thm_ConjCoord_Proof_two_sq_unique
public import Theorems.Thm_ConjCoord_Proof_gCount_eq_card
public import Theorems.Thm_ConjCoord_Proof_mem_gset
public import Theorems.Thm_ConjCoord_Proof_neg_cond
public import Theorems.Thm_ConjCoord_Proof_eight_dvd_card_k_ne
public import Theorems.Thm_ConjCoord_Proof_card_eq_two_mul_filter


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5) {a b : ℤ}
    (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    (gCount p : ℤ) ≡ 4 * octA b [ZMOD 8] := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hodd : (p : ℤ) % 2 = 1 := by omega
  have ha0 : a ≠ 0 := by
    rintro rfl; have := sq_mod16_ne5 b; simp at hab; omega
  have hb0 : b ≠ 0 := by
    rintro rfl; have := sq_mod16_ne5 a; simp at hab; omega
  rw [gCount_eq_card, ← card_filter_add_card_filter_not (s := gset p) (p := fun v => ¬ v.2.2 = 0)]
  obtain ⟨c, hc⟩ := eight_dvd_card_k_ne (m := p)
  set S0 := (gset p).filter fun v => ¬ ¬ v.2.2 = 0
  have hS0 : ∀ v ∈ S0, v ∈ gset p ∧ v.2.2 = 0 := fun v hv =>
    ⟨(mem_filter.mp hv).1, not_not.mp (mem_filter.mp hv).2⟩
  have h4 : S0.card = 4 * ((S0.filter fun v => 0 < v.1).filter fun v => 0 < v.2.1).card := by
    rw [card_eq_two_mul_filter S0 (fun v => (-v.1, v.2.1, v.2.2)) (fun v => 0 < v.1) ?_ ?_ ?_]
    · rw [card_eq_two_mul_filter _ (fun v => (v.1, -v.2.1, v.2.2)) (fun v => 0 < v.2.1) ?_ ?_ ?_]
      · ring
      · intro v hv
        simp only [mem_filter] at hv
        obtain ⟨hg, hk⟩ := hS0 v hv.1
        rw [mem_gset] at hg
        simp only [S0, mem_filter, mem_gset, neg_sq, neg_cond]
        exact ⟨⟨hg, by simpa using hk⟩, hv.2⟩
      · intro v _; simp
      · intro v hv
        simp only [mem_filter] at hv
        obtain ⟨hg, -⟩ := hS0 v hv.1
        rw [mem_gset] at hg
        have : v.2.1 ≠ 0 := by rintro h; rw [h] at hg; omega
        simp only; constructor <;> intro h <;> omega
    · intro v hv
      obtain ⟨hg, hk⟩ := hS0 v hv
      rw [mem_gset] at hg
      simp only [S0, mem_filter, mem_gset, neg_sq]
      exact ⟨hg, by simpa using hk⟩
    · intro v _; simp
    · intro v hv
      obtain ⟨hg, -⟩ := hS0 v hv
      rw [mem_gset] at hg
      have : v.1 ≠ 0 := by
        rintro h; rw [h] at hg; have := sq_mod16_ne5 v.2.1; simp at hg; omega
      simp only; constructor <;> intro h <;> omega
  set T := (S0.filter fun v => 0 < v.1).filter fun v => 0 < v.2.1
  have hT : ∀ v ∈ T, v.1 = |a| ∧ v.2.1 = |b| ∧ v.2.2 = 0 ∧ (v.2.1 % 16 = 6 ∨ v.2.1 % 16 = 10) := by
    intro v hv
    simp only [T, mem_filter] at hv
    obtain ⟨⟨hv0, h1⟩, h2⟩ := hv
    obtain ⟨hg, hk⟩ := hS0 v hv0
    rw [mem_gset, hk] at hg
    have hβe : Even v.2.1 := by
      rcases hg.2.2 with h | h <;> exact ⟨v.2.1 / 2, by omega⟩
    have hbe : Even |b| := (even_abs).mpr hb
    have := two_sq_unique hpZ hodd h1 h2 (abs_pos.mpr ha0) (abs_pos.mpr hb0)
      (by simpa using hg.1) (by rw [sq_abs, sq_abs]; exact hab) hβe hbe
    exact ⟨this.1, this.2, hk, hg.2.2⟩
  have habs : (|b| % 16 = 6 ∨ |b| % 16 = 10) ↔ (b % 16 = 6 ∨ b % 16 = 10) := by
    rcases abs_cases b with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h]; omega
  have hTcard : (T.card : ℤ) = octA b := by
    unfold octA
    split_ifs with hcond
    · have : T = {(|a|, |b|, 0)} := by
        ext v
        rw [mem_singleton]
        constructor
        · intro hv
          obtain ⟨h1, h2, h3, -⟩ := hT v hv
          ext <;> simp [h1, h2, h3]
        · rintro rfl
          simp only [T, S0, mem_filter, mem_gset]
          refine ⟨⟨⟨⟨?_, ?_, habs.mpr hcond⟩, by simp⟩, abs_pos.mpr ha0⟩, abs_pos.mpr hb0⟩
          · rw [sq_abs, sq_abs]; simpa using hab
          · rw [sq_abs, sq_abs, hab]; omega
      rw [this, card_singleton]; rfl
    · have : T = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro v hv
        obtain ⟨-, h2, -, h4⟩ := hT v hv
        rw [h2] at h4
        exact hcond (habs.mp h4)
      rw [this, card_empty]; rfl
  push_cast
  rw [hc, h4]
  push_cast
  rw [hTcard]
  exact Int.modEq_iff_dvd.mpr ⟨-c, by ring⟩
end ConjCoord.Proof
