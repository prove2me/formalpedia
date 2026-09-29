-- Prove2me | solution 1 for Diaz.balanced_jet_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:15:44.238238+00:00
-- url     : https://prove2.me/submissions/22a15979-e9a8-4aa3-84b3-15d7a7769dc7

import Mathlib

open ComplexConjugate

theorem aux_algebraMap_mk (K : Subfield ℂ) (a : ℂ) (h : a ∈ K) :
    (algebraMap (↥K) ℂ) ⟨a, h⟩ = a := rfl

theorem aux_zpow_mem_iff {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) (hu0 : u ≠ 0) (n : ℤ) :
    u ^ n ∈ K ↔ n = 0 := by
  constructor
  · intro hmem
    by_contra hn
    have halg : (u ^ n) ∈ algebraicClosure (↥K) ℂ := by
      refine mem_algebraicClosure_iff.2 ⟨Polynomial.X - Polynomial.C ⟨u ^ n, hmem⟩, ?_, ?_⟩
      · exact Polynomial.X_sub_C_ne_zero _
      · rw [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C,
          aux_algebraMap_mk, sub_self]
    have key : ∀ m : ℕ, 0 < m → u ^ m ∈ algebraicClosure (↥K) ℂ → False := by
      intro m hm hmem2
      exact hT (IsAlgebraic.of_pow hm (mem_algebraicClosure_iff.1 hmem2))
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · refine key (-n).toNat (by omega) ?_
      have he : u ^ ((-n).toNat) = (u ^ n)⁻¹ := by
        rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg]
      rw [he]
      exact inv_mem halg
    · refine key n.toNat (by omega) ?_
      have he : u ^ (n.toNat) = u ^ n := by
        rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      rw [he]
      exact halg
  · rintro rfl
    simpa using K.one_mem

theorem solution {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) (hu0 : u ≠ 0)
    (hρ : u * conj u ∈ K) {α : ℂ} (hα : α ∈ K) (hα0 : α ≠ 0) (j k : ℕ) :
    u ^ j * (conj u) ^ k * α ∈ K ↔ j = k := by
  have hcu : conj u ≠ 0 := by simpa using hu0
  have hconj : conj u = (u * conj u) / u := by field_simp
  set t : ℂ := (u * conj u) ^ k * α with ht
  have htK : t ∈ K := K.mul_mem (K.pow_mem hρ k) hα
  have ht0 : t ≠ 0 := mul_ne_zero (pow_ne_zero _ (mul_ne_zero hu0 hcu)) hα0
  have key : u ^ j * (conj u) ^ k * α = t * u ^ ((j : ℤ) - (k : ℤ)) := by
    rw [ht, zpow_sub₀ hu0, zpow_natCast, zpow_natCast]
    rw [hconj]
    field_simp
    ring
  rw [key]
  constructor
  · intro hm
    have : u ^ ((j : ℤ) - (k : ℤ)) ∈ K := by
      have := K.mul_mem (K.inv_mem htK) hm
      rwa [← mul_assoc, inv_mul_cancel₀ ht0, one_mul] at this
    have := (aux_zpow_mem_iff hT hu0 _).1 this
    omega
  · intro hjk
    subst hjk
    simpa using htK
