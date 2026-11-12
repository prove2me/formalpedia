-- Prove2me | solution 1 for BFFPyramidal.herzog_schonheim_pyramidal
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-13T18:51:46.678427+00:00
-- url     : https://prove2.me/submissions/5027093a-58f5-4200-bdd5-1df67ec74afd

import Theorems.Thm_BFFPyramidal_multiplicity_bound
import Theorems.Thm_BFFPyramidal_two_le_multiplicity_bound_arith

open BFFPyramidal

/-- In a coset partition with more than one part, not every part can be the whole group:
otherwise two distinct parts would both contain every element, contradicting uniqueness. -/
private lemma exists_ne_top {G : Type*} [Group G] {t : ℕ} (ht : 1 < t)
    (K : Fin t → Subgroup G) (a : Fin t → G) (hpart : IsCosetPartition K a) :
    ∃ i, K i ≠ ⊤ := by
  by_contra h
  push Not at h
  set i0 : Fin t := ⟨0, by omega⟩ with hi0
  set i1 : Fin t := ⟨1, ht⟩ with hi1
  have hne : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  obtain ⟨j, -, huniq⟩ := hpart (a i0)
  have e0 : (a i0)⁻¹ * a i0 ∈ K i0 := by simp [h i0]
  have e1 : (a i1)⁻¹ * a i0 ∈ K i1 := by simp [h i1]
  exact hne ((huniq i0 e0).trans (huniq i1 e1).symm)

/-- Hence the gcd of the orders is at most half of `|G|`, so the modulus is at least `2`. -/
private lemma two_le_modulus {G : Type*} [Group G] [Finite G] {t : ℕ} (ht : 1 < t)
    (K : Fin t → Subgroup G) (a : Fin t → G) (hpart : IsCosetPartition K a) :
    2 ≤ modulus K := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_ne_top ht K a hpart
  set g : ℕ := Finset.univ.gcd fun i => Nat.card (K i) with hg
  have hgdvd : g ∣ Nat.card (K i₀) := Finset.gcd_dvd (Finset.mem_univ i₀)
  have hpos : 0 < g := Nat.pos_of_dvd_of_pos hgdvd Nat.card_pos
  have hidx2 : 2 ≤ (K i₀).index := by
    have h1 : (K i₀).index ≠ 1 := fun h => hi₀ (Subgroup.index_eq_one.mp h)
    have h0 : (K i₀).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hmul : Nat.card (K i₀) * (K i₀).index = Nat.card G := Subgroup.card_mul_index _
  have h2g : 2 * g ≤ Nat.card G := by
    calc 2 * g ≤ (K i₀).index * Nat.card (K i₀) :=
          Nat.mul_le_mul hidx2 (Nat.le_of_dvd Nat.card_pos hgdvd)
      _ = Nat.card G := by rw [mul_comm]; exact hmul
  unfold modulus
  rw [← hg]
  exact (Nat.le_div_iff_mul_le hpos).mpr h2g

theorem solution {G : Type*} [Group G] [Finite G] (hG : IsPyramidal G)
    {t : ℕ} (ht : 1 < t) (K : Fin t → Subgroup G) (a : Fin t → G)
    (hpart : IsCosetPartition K a) :
    ∃ i j : Fin t, i ≠ j ∧ (K i).index = (K j).index := by
  classical
  obtain ⟨m, hm⟩ := multiplicity_bound hG ht K a hpart
  have h2 : 2 ≤ (maxPrimeFac (modulus K) * Nat.totient (modulus K)) / modulus K + 1 :=
    two_le_multiplicity_bound_arith _ (two_le_modulus ht K a hpart)
  have hcard : 2 ≤ (Finset.univ.filter fun i => Nat.card (K i) = m).card := le_trans h2 hm
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
  refine ⟨i, j, hij, ?_⟩
  have hKi : Nat.card (K i) = m := (Finset.mem_filter.mp hi).2
  have hKj : Nat.card (K j) = m := (Finset.mem_filter.mp hj).2
  have ei : m * (K i).index = Nat.card G := by
    rw [← hKi]; exact Subgroup.card_mul_index _
  have ej : m * (K j).index = Nat.card G := by
    rw [← hKj]; exact Subgroup.card_mul_index _
  have hmpos : 0 < m := by rw [← hKi]; exact Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hmpos (ei.trans ej.symm)
