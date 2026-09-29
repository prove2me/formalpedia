-- Prove2me | solution 1 for Erdos142.exists_density_limit
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:31:57.05102+00:00
-- url     : https://prove2.me/submissions/d1d0f45c-ef48-4734-aa60-44ad2130e95d

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

private theorem scout_r_small (k N : ℕ) (hk : k ≤ 1) : r k N = N := by
  apply le_antisymm (r_le k N)
  have h : Erdos142.IsAPOfLengthFree (Finset.Icc 1 N : Set ℕ) k := by
    intro t ht ha
    exact_mod_cast hk
  simpa using le_r (S := Finset.Icc 1 N) (by rfl) h

private theorem scout_r_add (k M N : ℕ) : r k (M + N) ≤ r k M + r k N := by
  by_cases hk : k ≤ 1
  · simp [scout_r_small k _ hk]
  have hk2 : 2 ≤ k := by omega
  apply csSup_le
  · exact ⟨0, ∅, by simp, (by simpa using isAPOfLengthFree_empty (α := ℕ) k), by simp⟩
  · rintro m ⟨S,hS,hf,rfl⟩
    let L := S.filter (fun x => x ≤ M)
    let R := S.filter (fun x => ¬ x ≤ M)
    let T := R.image (fun x => x-M)
    have hL : L ⊆ Finset.Icc 1 M := by
      intro x hx
      obtain ⟨hxs,hxm⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hS hxs)).1,hxm⟩
    have hLf : Erdos142.IsAPOfLengthFree (L : Set ℕ) k := by
      intro t ht hap
      exact hf t (fun x hx => (Finset.mem_filter.mp (ht hx)).1) hap
    have hT : T ⊆ Finset.Icc 1 N := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hys,hym⟩ := Finset.mem_filter.mp hy
      have hymax := Finset.mem_Icc.mp (hS hys)
      apply Finset.mem_Icc.mpr
      omega
    have hTf : Erdos142.IsAPOfLengthFree (T : Set ℕ) k := by
      apply (scout_apFree_iff k hk2 T).mp
      intro ⟨a,d,hd,ha⟩
      apply (scout_apFree_iff k hk2 S).mpr hf
      refine ⟨a+M,d,hd,?_⟩
      intro i hi
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp (ha i hi)
      obtain ⟨hys,hym⟩ := Finset.mem_filter.mp hy
      have hye : y = (a+M)+i*d := by omega
      rw [← hye]
      exact hys
    have hcard : T.card = R.card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy hxy
      have hxm := (Finset.mem_filter.mp hx).2
      have hym := (Finset.mem_filter.mp hy).2
      change x-M = y-M at hxy
      omega
    have hsplit : L.card + R.card = S.card := Finset.card_filter_add_card_filter_not (s := S) _
    have hl := le_r hL hLf
    have ht := le_r hT hTf
    omega

theorem solution (k : ℕ) (_hk : 0 < k) :
    ∃ c : ℝ, Filter.Tendsto (fun N : ℕ => (r k N : ℝ) / (N : ℝ)) Filter.atTop (nhds c) := by
  have hs : Subadditive (fun n : ℕ => (r k n : ℝ)) := by
    intro m n
    change (r k (m+n) : ℝ) ≤ (r k m : ℝ) + (r k n : ℝ)
    exact_mod_cast scout_r_add k m n
  refine ⟨hs.lim, hs.tendsto_lim ?_⟩
  refine ⟨0, ?_⟩
  rintro x ⟨n,rfl⟩
  positivity

#print axioms solution
