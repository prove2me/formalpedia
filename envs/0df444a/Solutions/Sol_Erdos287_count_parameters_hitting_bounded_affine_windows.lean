-- Prove2me | solution 1 for Erdos287.count_parameters_hitting_bounded_affine_windows
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T09:22:18.546806+00:00
-- url     : https://prove2.me/submissions/3128d260-d89a-4330-8c48-0aa0ac6d41c9

import Mathlib

open Finset

set_option autoImplicit false

/-- If each parameter hits a marked position in some affine window of bounded
width, the number of parameters is bounded by the number of marked positions. -/
theorem solution (S G : Finset ℕ) (N B : ℕ) (C : Fin N → ℕ) (g : ℕ → ℕ)
    (hC : ∀ j, 0 < C j)
    (hcover : ∀ t ∈ S, ∃ j : Fin N, ∃ i ∈ G, C j * t ≤ g i ∧ g i ≤ C j * t + B) :
    S.card ≤ (B + 1) * N * G.card := by
  classical
  have hex (t : S) : ∃ a : Fin N × ℕ, a.2 ∈ G ∧
      C a.1 * t.val ≤ g a.2 ∧ g a.2 ≤ C a.1 * t.val + B := by
    obtain ⟨j, i, hi, hlo, hhi⟩ := hcover t.val t.property
    exact ⟨(j, i), hi, hlo, hhi⟩
  choose pick hpick using hex
  by_cases hS : S.Nonempty
  · let f (t : ℕ) : Fin N × ℕ := if ht : t ∈ S then pick ⟨t, ht⟩ else pick ⟨S.min' hS, S.min'_mem hS⟩
    have hf {t : ℕ} (ht : t ∈ S) : (f t).2 ∈ G ∧
        C (f t).1 * t ≤ g (f t).2 ∧ g (f t).2 ≤ C (f t).1 * t + B := by
      simpa only [f, dif_pos ht] using hpick ⟨t, ht⟩
    have hmaps : ∀ t ∈ S, f t ∈ (univ : Finset (Fin N)) ×ˢ G := by
      intro t ht
      exact mem_product.mpr ⟨mem_univ _, (hf ht).1⟩
    have hfibers (a : Fin N × ℕ) (_ha : a ∈ (univ : Finset (Fin N)) ×ˢ G) :
        (S.filter (fun t => f t = a)).card ≤ B + 1 := by
      let u := g a.2 / C a.1
      have hsub : S.filter (fun t => f t = a) ⊆ Icc (u - B) u := by
        intro t ht
        obtain ⟨htS, hta⟩ := mem_filter.mp ht
        have hh := hf htS
        rw [hta] at hh
        have hlo : t ≤ u := (Nat.le_div_iff_mul_le (hC a.1)).mpr (by
          simpa only [Nat.mul_comm] using hh.2.1)
        have hbound : g a.2 ≤ C a.1 * (t + B) := calc
          g a.2 ≤ C a.1 * t + B := hh.2.2
          _ ≤ C a.1 * (t + B) := by
            rw [Nat.mul_add]
            exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (hC a.1)) _
        have hhi : u ≤ t + B :=
          (Nat.div_le_div_right hbound).trans_eq (Nat.mul_div_cancel_left _ (hC a.1))
        exact mem_Icc.mpr ⟨by omega, hlo⟩
      exact (card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
    simpa only [card_product, card_univ, Fintype.card_fin, mul_assoc] using
      (card_le_mul_card_image_of_maps_to hmaps (B + 1) hfibers)
  · simpa [not_nonempty_iff_eq_empty.mp hS]

