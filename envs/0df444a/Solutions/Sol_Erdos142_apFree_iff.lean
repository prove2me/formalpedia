-- Prove2me | solution 1 for Erdos142.apFree_iff
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:31:54.749659+00:00
-- url     : https://prove2.me/submissions/2ab3c0f9-58e8-499b-ae6a-404225c080a9

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

theorem solution (k : ℕ) (hk : 2 ≤ k) (A : Finset ℕ) :
    APFree k A ↔ Erdos142.IsAPOfLengthFree (A : Set ℕ) k :=
  scout_apFree_iff k hk A

#print axioms solution
