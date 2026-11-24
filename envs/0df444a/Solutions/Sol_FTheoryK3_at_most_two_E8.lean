-- Prove2me | solution 1 for FTheoryK3.at_most_two_E8
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-21T20:10:59.855986+00:00
-- url     : https://prove2.me/submissions/38651a0b-e4fb-4847-954e-16ae19b8bfa0

import Definitions.Def_FTheoryK3Core

open Polynomial

namespace FTheoryK3Aux

variable {R : Type*} [CommRing R]

lemma rootMultiplicity_neg [IsDomain R] (a : R) (p : R[X]) :
    rootMultiplicity a (-p) = rootMultiplicity a p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · have : -p = C (-1) * p := by simp [C_neg, C_1, neg_mul]
    rw [this, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)) hp),
      rootMultiplicity_C, zero_add]

lemma rootMultiplicity_pow [IsDomain R] (a : R) (p : R[X]) (n : ℕ) :
    rootMultiplicity a (p ^ n) = n * rootMultiplicity a p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases eq_or_ne p 0 with rfl | hp
      · rw [zero_pow (Nat.succ_ne_zero n), rootMultiplicity_zero, Nat.mul_zero]
      · rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp), ih, Nat.succ_mul]

lemma rootMultiplicity_add_of_lt (a : R) {p q : R[X]} (hzero : p + q ≠ 0) (hq : q ≠ 0)
    (h : rootMultiplicity a q < rootMultiplicity a p) :
    rootMultiplicity a (p + q) = rootMultiplicity a q := by
  apply le_antisymm
  · rw [rootMultiplicity_le_iff hzero]
    intro hdvd
    have hp : (X - C a) ^ (rootMultiplicity a q + 1) ∣ p :=
      (pow_dvd_pow (X - C a) (Nat.succ_le_of_lt h)).trans (pow_rootMultiplicity_dvd p a)
    have hq' : (X - C a) ^ (rootMultiplicity a q + 1) ∣ q := by
      have := dvd_sub hdvd hp
      rwa [show p + q - p = q by ring] at this
    exact pow_rootMultiplicity_not_dvd hq a hq'
  · calc rootMultiplicity a q = min (rootMultiplicity a p) (rootMultiplicity a q) :=
          (min_eq_right (le_of_lt h)).symm
      _ ≤ rootMultiplicity a (p + q) := rootMultiplicity_add a hzero

variable {k : Type*} [Field k]

lemma discriminant_natDegree_le (f g : k[X]) (hf : f.natDegree ≤ 8) (hg : g.natDegree ≤ 12) :
    (FTheoryK3.Δ f g).natDegree ≤ 24 := by
  unfold FTheoryK3.Δ
  compute_degree
  omega

lemma sum_rootMultiplicity_discriminant_le (f g : k[X]) (_h : FTheoryK3.Δ f g ≠ 0)
    (S : Finset k) :
    (∑ t₀ ∈ S, (FTheoryK3.Δ f g).rootMultiplicity t₀) ≤ (FTheoryK3.Δ f g).natDegree := by
  classical
  calc ∑ t₀ ∈ S, (FTheoryK3.Δ f g).rootMultiplicity t₀
      = ∑ t₀ ∈ S, (FTheoryK3.Δ f g).roots.count t₀ := by simp only [count_roots]
    _ ≤ ∑ t₀ ∈ S ∪ (FTheoryK3.Δ f g).roots.toFinset, (FTheoryK3.Δ f g).roots.count t₀ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun i _ _ => Nat.zero_le _)
    _ = (FTheoryK3.Δ f g).roots.card :=
        Multiset.sum_count_eq_card (fun a ha => Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ (FTheoryK3.Δ f g).natDegree := card_roots' _

variable [CharZero k]

lemma rootMultiplicity_discriminant_of_isE8Point (f g : k[X]) (t₀ : k)
    (h : FTheoryK3.IsE8Point f g t₀) :
    (FTheoryK3.Δ f g).rootMultiplicity t₀ = 10 := by
  obtain ⟨hf4, hg5⟩ := h
  have hf0 : f ≠ 0 := fun h0 => by simp [h0] at hf4
  have hg0 : g ≠ 0 := fun h0 => by simp [h0] at hg5
  have h4 : (4 : k[X]) = C (4 : k) := (C_eq_natCast 4).symm
  have h27 : (27 : k[X]) = C (27 : k) := (C_eq_natCast 27).symm
  have hf3 : rootMultiplicity t₀ (f ^ 3) = 3 * rootMultiplicity t₀ f :=
    rootMultiplicity_pow t₀ f 3
  have hg2 : rootMultiplicity t₀ (g ^ 2) = 2 * rootMultiplicity t₀ g :=
    rootMultiplicity_pow t₀ g 2
  have hA : rootMultiplicity t₀ (4 * f ^ 3) = 3 * rootMultiplicity t₀ f := by
    rw [h4, rootMultiplicity_mul (by simp [hf0]), rootMultiplicity_C, zero_add, hf3]
  have hB : rootMultiplicity t₀ (27 * g ^ 2) = 10 := by
    rw [h27, rootMultiplicity_mul (by simp [hg0]), rootMultiplicity_C, zero_add, hg2, hg5]
  have hne : FTheoryK3.Δ f g ≠ 0 := by
    intro hzero
    rw [FTheoryK3.Δ] at hzero
    have h1 : (4 : k[X]) * f ^ 3 = -((27 : k[X]) * g ^ 2) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hzero
    have hthis : rootMultiplicity t₀ (4 * f ^ 3) = rootMultiplicity t₀ (27 * g ^ 2) := by
      rw [h1, rootMultiplicity_neg]
    rw [hA, hB] at hthis
    have : 12 ≤ 3 * rootMultiplicity t₀ f := by omega
    omega
  rw [FTheoryK3.Δ,
    rootMultiplicity_add_of_lt t₀ hne (by simp [hg0]) (by rw [hB, hA]; omega), hB]

end FTheoryK3Aux

open FTheoryK3

variable {k : Type*} [Field k] [CharZero k]

/-- **Elliptic K3 surfaces: at most two E₈ points.** For Calabi–Yau/K3 Weierstrass data
`f, g` (degrees ≤ 8, ≤ 12, discriminant ≠ 0), the base points carrying a Kodaira type II*
fibre (E₈ gauge algebra, i.e. `ord f ≥ 4` and `ord g = 5`) form a finite set of cardinality
at most two. -/
theorem solution (f g : k[X]) (h : IsK3Data f g) :
    {t₀ : k | IsE8Point f g t₀}.Finite ∧
    Nat.card {t₀ : k | IsE8Point f g t₀} ≤ 2 := by
  obtain ⟨hf8, hg12, hΔ⟩ := h
  have hE8 : ∀ t₀ ∈ {t₀ : k | IsE8Point f g t₀}, (Δ f g).rootMultiplicity t₀ = 10 :=
    fun t₀ ht => FTheoryK3Aux.rootMultiplicity_discriminant_of_isE8Point f g t₀ ht
  have hroot : ∀ t₀ ∈ {t₀ : k | IsE8Point f g t₀}, (Δ f g).IsRoot t₀ := by
    intro t₀ ht
    have hpos : 0 < (Δ f g).rootMultiplicity t₀ := by rw [hE8 t₀ ht]; norm_num
    exact (rootMultiplicity_pos'.mp hpos).2
  have hfin : {t₀ : k | IsE8Point f g t₀}.Finite :=
    (finite_setOfPred_isRoot hΔ).subset hroot
  refine ⟨hfin, ?_⟩
  have h10 : ∑ t₀ ∈ hfin.toFinset,
      (Δ f g).rootMultiplicity t₀ = 10 * hfin.toFinset.card := by
    rw [Finset.sum_congr rfl (fun t₀ ht => hE8 t₀ (hfin.mem_toFinset.mp ht))]
    simp [Finset.sum_const, mul_comm]
  have hsum := FTheoryK3Aux.sum_rootMultiplicity_discriminant_le f g hΔ hfin.toFinset
  have hdeg : (Δ f g).natDegree ≤ 24 := FTheoryK3Aux.discriminant_natDegree_le f g hf8 hg12
  have hcard : 10 * hfin.toFinset.card ≤ 24 := by
    rw [← h10]
    exact le_trans hsum hdeg
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  omega

#check @solution
#print axioms solution
