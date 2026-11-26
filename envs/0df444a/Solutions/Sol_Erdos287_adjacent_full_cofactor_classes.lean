-- Prove2me | solution 1 for Erdos287.adjacent_full_cofactor_classes
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:57:18.455352+00:00
-- url     : https://prove2.me/submissions/cc338138-e811-46c1-8ad9-9b182eaad2c9

import Mathlib
import Theorems.Thm_Erdos287_full_cofactor_residue_table

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1700000

/-- Adjacent omissions can be certified over the full carry periods of
both prime-power layers, with no restriction on the size of a pattern. -/
theorem solution (p r e g a b i j h k : ℕ) (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (he : 1 ≤ e) (hg : 1 ≤ g) (ha : 0 < a) (hb : 0 < b)
    (hadj : (a + i) * p ^ e + 1 = (b + j) * r ^ g)
    (F G : Finset (Finset ℕ))
    (hF : ∀ T ∈ F, ∀ x ∈ T, ∀ y ∈ T, x < y + p ^ (h + 1))
    (hG : ∀ T ∈ G, ∀ x ∈ T, ∀ y ∈ T, x < y + r ^ (k + 1)) :
    let P := p ^ (2 * h + 1)
    let Q := r ^ (2 * k + 1)
    ∃ (Rp : Finset (ZMod P)) (Rr : Finset (ZMod Q)) (B : Finset (ZMod (P * Q))),
      (∀ z : ZMod P, z ∈ Rp ↔ ∃ T ∈ F, T.Nonempty ∧
        let c := z.val + P
        let L := ∏ d ∈ T, (c + d)
        p ^ (padicValNat p L + 1) ∣ ∑ u ∈ T, ∏ d ∈ T.erase u, (c + d)) ∧
      (∀ z : ZMod Q, z ∈ Rr ↔ ∃ T ∈ G, T.Nonempty ∧
        let c := z.val + Q
        let L := ∏ d ∈ T, (c + d)
        r ^ (padicValNat r L + 1) ∣ ∑ u ∈ T, ∏ d ∈ T.erase u, (c + d)) ∧
      B.card = (P - Rp.card) * (Q - Rr.card) ∧
      (∀ t : ℕ, (t : ZMod (P * Q)) ∈ B ↔
        ((a + r ^ g * t : ℕ) : ZMod P) ∉ Rp ∧ ((b + p ^ e * t : ℕ) : ZMod Q) ∉ Rr) ∧
      ∀ t : ℕ, (t : ZMod (P * Q)) ∈ B →
        ∀ D : Finset ℕ, (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
        (∃ T ∈ F, T.image (fun d => (a + r ^ g * t + d) * p ^ e) =
          D.filter (fun n => p ^ e ∣ n)) →
        (∃ U ∈ G, U.image (fun d => (b + p ^ e * t + d) * r ^ g) =
          D.filter (fun n => r ^ g ∣ n)) →
        let x := (a + r ^ g * t + i) * p ^ e
        x ∉ D ∧ x + 1 ∉ D := by
  classical
  intro P Q
  have : NeZero P := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero Q := ⟨pow_ne_zero _ hr.ne_zero⟩
  have hcop := (Nat.coprime_primes hp hr).mpr hpr
  have hPQ : P.Coprime Q := (hcop.pow_left _).pow_right _
  have hl : (r ^ g).Coprime P := (hcop.symm.pow_left g).pow_right _
  have hr' : (p ^ e).Coprime Q := (hcop.pow_left e).pow_right _
  obtain ⟨Rp, hRp, hpCheck⟩ := Erdos287.full_cofactor_residue_table p h hp F hF
  obtain ⟨Rr, hRr, hrCheck⟩ := Erdos287.full_cofactor_residue_table r k hr G hG
  let L := (ZMod.unitOfCoprime (r ^ g) hl).mulLeft.trans (Equiv.addLeft (a : ZMod P))
  let R := (ZMod.unitOfCoprime (p ^ e) hr').mulLeft.trans (Equiv.addLeft (b : ZMod Q))
  let C := ZMod.chineseRemainder hPQ
  let E := C.toEquiv.trans (L.prodCongr R)
  let U := (univ \ Rp) ×ˢ (univ \ Rr)
  let B := U.map E.symm.toEmbedding
  have hE (t : ℕ) : E (t : ZMod (P * Q)) =
      (((a + r ^ g * t : ℕ) : ZMod P), ((b + p ^ e * t : ℕ) : ZMod Q)) := by
    have hC : C (t : ZMod (P * Q)) = ((t : ZMod P), (t : ZMod Q)) := by
      rw [map_natCast]
      rfl
    change (L (C (t : ZMod (P * Q))).1, R (C (t : ZMod (P * Q))).2) = _
    rw [hC]
    simp [L, R, ZMod.coe_unitOfCoprime]
  have hmem (t : ℕ) : (t : ZMod (P * Q)) ∈ B ↔
      ((a + r ^ g * t : ℕ) : ZMod P) ∉ Rp ∧ ((b + p ^ e * t : ℕ) : ZMod Q) ∉ Rr := by
    have hmap : (t : ZMod (P * Q)) ∈ B ↔ E (t : ZMod (P * Q)) ∈ U := by
      constructor
      · intro ht
        obtain ⟨z, hz, heq⟩ := mem_map.mp ht
        change E.symm z = (t : ZMod (P * Q)) at heq
        rwa [← heq, E.apply_symm_apply]
      · intro ht
        exact mem_map.mpr ⟨_, ht, E.symm_apply_apply _⟩
    rw [hmap, hE]
    simp [U]
  refine ⟨Rp, Rr, B, hRp, hRr, ?_, hmem, ?_⟩
  · rw [show B = U.map E.symm.toEmbedding from rfl, card_map, show U = _ from rfl, card_product,
      card_sdiff_of_subset (subset_univ Rp), card_sdiff_of_subset (subset_univ Rr), card_univ,
      card_univ, ZMod.card, ZMod.card]
  · intro t ht D hpos hsum hleft hright
    obtain ⟨hnotL, hnotR⟩ := (hmem t).mp ht
    obtain ⟨T, hT, hshapeT⟩ := hleft
    obtain ⟨V, hV, hshapeV⟩ := hright
    have hT0 : T = ∅ := by
      by_contra hne
      exact hnotL (hpCheck D e (a + r ^ g * t) he (by omega) hpos hsum T hT hshapeT
        (nonempty_iff_ne_empty.mpr hne))
    have hV0 : V = ∅ := by
      by_contra hne
      exact hnotR (hrCheck D g (b + p ^ e * t) hg (by omega) hpos hsum V hV hshapeV
        (nonempty_iff_ne_empty.mpr hne))
    have hleft0 : D.filter (fun n => p ^ e ∣ n) = ∅ := by rw [← hshapeT, hT0, image_empty]
    have hright0 : D.filter (fun n => r ^ g ∣ n) = ∅ := by rw [← hshapeV, hV0, image_empty]
    let x := (a + r ^ g * t + i) * p ^ e
    change x ∉ D ∧ x + 1 ∉ D
    have hdiff : x + 1 = (b + p ^ e * t + j) * r ^ g := by
      calc
        x + 1 = (a + i) * p ^ e + 1 + r ^ g * p ^ e * t := by dsimp [x]; ring
        _ = _ := by rw [hadj]; ring
    constructor
    · intro hx
      have hh : x ∈ D.filter (fun n => p ^ e ∣ n) :=
        mem_filter.mpr ⟨hx, dvd_mul_left _ _⟩
      simp [hleft0] at hh
    · intro hx
      have hh : x + 1 ∈ D.filter (fun n => r ^ g ∣ n) :=
        mem_filter.mpr ⟨hx, by rw [hdiff]; exact dvd_mul_left _ _⟩
      simp [hright0] at hh

