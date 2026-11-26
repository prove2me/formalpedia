-- Prove2me | solution 1 for Erdos287.adjacent_cofactor_classes
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:43:12.20217+00:00
-- url     : https://prove2.me/submissions/3e892b7b-88ca-46c6-a8f5-d93a7c81594e

import Mathlib
import Theorems.Thm_Erdos287_cofactor_translation_residues

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Standard Chinese remainder shifts preserve adjacency. If each prime-power
layer must use one of the supplied cofactor patterns, many joint residue
classes certify both omissions. -/
theorem solution (p r e g a b i j : ℕ) (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (he : 1 ≤ e) (hg : 1 ≤ g) (ha : 0 < a) (hb : 0 < b)
    (hadj : (a + i) * p ^ e + 1 = (b + j) * r ^ g)
    (F G : Finset (Finset ℕ))
    (hF : ∀ T ∈ F, T.card < p) (hG : ∀ T ∈ G, T.card < r) :
    ∃ B : Finset (ZMod (p * r)),
      (p - ∑ T ∈ F, (T.card - 1)) * (r - ∑ U ∈ G, (U.card - 1)) ≤ B.card ∧
      ∀ t : ℕ, (t : ZMod (p * r)) ∈ B →
        ∀ D : Finset ℕ, (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
        (∃ T ∈ F, T.image (fun d => (a + r ^ g * t + d) * p ^ e) =
          D.filter (fun n => p ^ e ∣ n)) →
        (∃ U ∈ G, U.image (fun d => (b + p ^ e * t + d) * r ^ g) =
          D.filter (fun n => r ^ g ∣ n)) →
        let x := (a + r ^ g * t + i) * p ^ e
        x ∉ D ∧ x + 1 ∉ D := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hp0 : NeZero p := ⟨hp.ne_zero⟩
  have hr0 : NeZero r := ⟨hr.ne_zero⟩
  obtain ⟨Rp, hpLim, _, hpCheck⟩ := (Erdos287.cofactor_translation_residues p hp).2 F hF
  obtain ⟨Rr, hrLim, _, hrCheck⟩ := (Erdos287.cofactor_translation_residues r hr).2 G hG
  have hpc : (r : ZMod p) ≠ 0 :=
    fun hz => hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp
      ((ZMod.natCast_eq_zero_iff r p).mp hz))
  have hrc : (p : ZMod r) ≠ 0 :=
    fun hz => hpr ((Nat.prime_dvd_prime_iff_eq hr hp).mp
      ((ZMod.natCast_eq_zero_iff p r).mp hz)).symm
  let L := (Equiv.mulLeft₀ ((r : ZMod p) ^ g) (pow_ne_zero _ hpc)).trans
    (Equiv.addLeft (a : ZMod p))
  let R := (Equiv.mulLeft₀ ((p : ZMod r) ^ e) (pow_ne_zero _ hrc)).trans
    (Equiv.addLeft (b : ZMod r))
  let C := ZMod.chineseRemainder ((Nat.coprime_primes hp hr).mpr hpr)
  let E := C.toEquiv.trans (L.prodCongr R)
  let U := (univ \ Rp) ×ˢ (univ \ Rr)
  let B := U.map E.symm.toEmbedding
  have hE (t : ℕ) : E (t : ZMod (p * r)) =
      (((a + r ^ g * t : ℕ) : ZMod p), ((b + p ^ e * t : ℕ) : ZMod r)) := by
    have hC : C (t : ZMod (p * r)) = ((t : ZMod p), (t : ZMod r)) := by
      rw [map_natCast]
      rfl
    change (L (C (t : ZMod (p * r))).1, R (C (t : ZMod (p * r))).2) = _
    rw [hC]
    simp [L, R, Nat.cast_pow]
  refine ⟨B, ?_, ?_⟩
  · have hpB : p - (∑ T ∈ F, (T.card - 1)) ≤ (univ \ Rp).card := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card]
      omega
    have hrB : r - (∑ U ∈ G, (U.card - 1)) ≤ (univ \ Rr).card := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card]
      omega
    rw [show B = U.map E.symm.toEmbedding from rfl, card_map, show U = _ from rfl, card_product]
    exact Nat.mul_le_mul hpB hrB
  · intro t ht D hpos hsum hleft hright
    obtain ⟨z, hz, heq⟩ := mem_map.mp ht
    change E.symm z = (t : ZMod (p * r)) at heq
    have hz' : E (t : ZMod (p * r)) ∈ U := by rwa [← heq, E.apply_symm_apply]
    rw [hE] at hz'
    obtain ⟨hc, hd⟩ := mem_product.mp hz'
    have hnotL : ((a + r ^ g * t : ℕ) : ZMod p) ∉ Rp := (mem_sdiff.mp hc).2
    have hnotR : ((b + p ^ e * t : ℕ) : ZMod r) ∉ Rr := (mem_sdiff.mp hd).2
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
      simpa only [hleft0, notMem_empty] using hh
    · intro hx
      have hh : x + 1 ∈ D.filter (fun n => r ^ g ∣ n) :=
        mem_filter.mpr ⟨hx, by rw [hdiff]; exact dvd_mul_left _ _⟩
      simpa only [hright0, notMem_empty] using hh

