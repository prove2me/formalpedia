-- Prove2me | solution 1 for FTheoryK3.rootMultiplicity_discriminant_of_isE8Point
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-21T20:09:24.258377+00:00
-- url     : https://prove2.me/submissions/b8967f7d-0186-4119-8455-478731a71a2a

import Definitions.Def_FTheoryK3Core

open Polynomial

namespace K3Aux

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

end K3Aux

open FTheoryK3

variable {k : Type*} [Field k] [CharZero k]

theorem solution (f g : k[X]) (t₀ : k) (h : IsE8Point f g t₀) :
    (Δ f g).rootMultiplicity t₀ = 10 := by
  obtain ⟨hf4, hg5⟩ := h
  have hf0 : f ≠ 0 := fun h0 => by simp [h0] at hf4
  have hg0 : g ≠ 0 := fun h0 => by simp [h0] at hg5
  have h4 : (4 : k[X]) = C (4 : k) := (C_eq_natCast 4).symm
  have h27 : (27 : k[X]) = C (27 : k) := (C_eq_natCast 27).symm
  have hf3 : rootMultiplicity t₀ (f ^ 3) = 3 * rootMultiplicity t₀ f :=
    K3Aux.rootMultiplicity_pow t₀ f 3
  have hg2 : rootMultiplicity t₀ (g ^ 2) = 2 * rootMultiplicity t₀ g :=
    K3Aux.rootMultiplicity_pow t₀ g 2
  have hA : rootMultiplicity t₀ (4 * f ^ 3) = 3 * rootMultiplicity t₀ f := by
    rw [h4, rootMultiplicity_mul (by simp [hf0]), rootMultiplicity_C, zero_add, hf3]
  have hB : rootMultiplicity t₀ (27 * g ^ 2) = 10 := by
    rw [h27, rootMultiplicity_mul (by simp [hg0]), rootMultiplicity_C, zero_add, hg2, hg5]
  have hne : Δ f g ≠ 0 := by
    intro hzero
    rw [Δ] at hzero
    have h1 : (4 : k[X]) * f ^ 3 = -((27 : k[X]) * g ^ 2) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hzero
    have hthis : rootMultiplicity t₀ (4 * f ^ 3) = rootMultiplicity t₀ (27 * g ^ 2) := by
      rw [h1, K3Aux.rootMultiplicity_neg]
    rw [hA, hB] at hthis
    have : 12 ≤ 3 * rootMultiplicity t₀ f := by omega
    omega
  rw [Δ, K3Aux.rootMultiplicity_add_of_lt t₀ hne (by simp [hg0]) (by rw [hB, hA]; omega), hB]

#check @solution
#print axioms solution
