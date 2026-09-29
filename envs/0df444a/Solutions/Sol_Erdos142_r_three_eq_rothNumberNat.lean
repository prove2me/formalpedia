-- Prove2me | solution 1 for Erdos142.r_three_eq_rothNumberNat
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:31:57.837249+00:00
-- url     : https://prove2.me/submissions/a054f935-64a4-400d-b688-b88f0b47b964

import Definitions.Def_Erdos142Basic

open Erdos142

private theorem scout_progression (k a d : ℕ) (hd : 0 < d) :
    Erdos142.IsAPOfLength ((Finset.range k).image (fun n => a + n*d) : Set ℕ) k := by
  refine ⟨a, d, ?_, ?_⟩
  · have hi : Function.Injective (fun n : ℕ => a + n*d) := by
      intro i j hij
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    simp [Finset.card_image_of_injective _ hi]
  · ext x
    simp [nsmul_eq_mul]

private theorem scout_apFree_iff (k : ℕ) (hk : 2 ≤ k) (A : Finset ℕ) :
    APFree k A ↔ Erdos142.IsAPOfLengthFree (A : Set ℕ) k := by
  constructor
  · intro h t ht hap
    obtain ⟨a,d,hcard,hrep⟩ := hap
    by_contra hsmall
    apply h
    have hd : 0 < d := by
      by_contra hnot
      have hz : d = 0 := by omega
      have hx (x : t) : (x : ℕ) = a := by
        have hh := (Set.ext_iff.mp hrep (x : ℕ)).mp x.property
        obtain ⟨i, _, hh⟩ := hh
        simpa [hz] using hh.symm
      have hu : Function.Injective (fun _ : t => ()) := by
        intro x y _
        exact Subtype.ext ((hx x).trans (hx y).symm)
      have hle := ENat.card_le_card_of_injective hu
      have hkle : (k : ℕ∞) ≤ 1 := by simpa [hcard] using hle
      exact hsmall hkle
    refine ⟨a,d,hd,?_⟩
    intro i hi
    apply ht
    rw [hrep]
    exact ⟨i, by exact_mod_cast hi, by simp [nsmul_eq_mul]⟩
  · intro h ⟨a,d,hd,ha⟩
    have ht : ((Finset.range k).image (fun n => a + n*d) : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact ha i (Finset.mem_range.mp hi)
    have hk1 := h _ ht (scout_progression k a d hd)
    have : k ≤ 1 := by exact_mod_cast hk1
    omega

private theorem scout_three_iff (A : Finset ℕ) :
    Erdos142.IsAPOfLengthFree (A : Set ℕ) (3 : ℕ) ↔ ThreeAPFree (A : Set ℕ) := by
  rw [← scout_apFree_iff 3 (by omega)]
  constructor
  · intro hf a ha b hb c hc he
    by_contra hab
    apply hf
    rcases lt_or_gt_of_ne hab with hab | hab
    · refine ⟨a,b-a,by omega,?_⟩
      intro i hi
      rcases (show i=0 ∨ i=1 ∨ i=2 by omega) with rfl | rfl | rfl
      · simpa using ha
      · have heq : a + 1*(b-a) = b := by omega
        simpa only [heq, Finset.mem_coe] using hb
      · have heq : a + 2*(b-a) = c := by omega
        simpa only [heq, Finset.mem_coe] using hc
    · refine ⟨c,b-c,by omega,?_⟩
      intro i hi
      rcases (show i=0 ∨ i=1 ∨ i=2 by omega) with rfl | rfl | rfl
      · simpa using hc
      · have heq : c + 1*(b-c) = b := by omega
        simpa only [heq, Finset.mem_coe] using hb
      · have heq : c + 2*(b-c) = a := by omega
        simpa only [heq, Finset.mem_coe] using ha
  · intro hf ⟨a,d,hd,ha⟩
    have h := hf (ha 0 (by omega)) (ha 1 (by omega)) (ha 2 (by omega)) (by omega)
    omega

private theorem scout_r_three (N : ℕ) : r 3 N = rothNumberNat N := by
  have he : r 3 N = addRothNumber (Finset.Icc 1 N) := by
    apply le_antisymm
    · apply csSup_le
      · exact ⟨0, ∅, by simp, (by simpa using isAPOfLengthFree_empty (α := ℕ) 3), by simp⟩
      · rintro m ⟨S,hS,hf,rfl⟩
        exact ((scout_three_iff S).mp hf).le_addRothNumber hS
    · obtain ⟨S,hS,hcard,hf⟩ := addRothNumber_spec (Finset.Icc 1 N)
      rw [← hcard]
      exact le_r hS ((scout_three_iff S).mpr hf)
  have hI : Finset.Icc 1 N = Finset.Ico 1 (N+1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [he, hI, addRothNumber_Ico]
  congr 1

theorem solution (N : ℕ) : r 3 N = rothNumberNat N := scout_r_three N

#print axioms solution
