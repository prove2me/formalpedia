-- Prove2me | solution 1 for Diaz.zpow_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:15:43.683979+00:00
-- url     : https://prove2.me/submissions/132c3881-ac72-4353-8a1a-8cfbc2598f4d

import Mathlib

open ComplexConjugate

theorem aux_algebraMap_mk (K : Subfield ℂ) (a : ℂ) (h : a ∈ K) :
    (algebraMap (↥K) ℂ) ⟨a, h⟩ = a := rfl

theorem solution {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) (hu0 : u ≠ 0) (n : ℤ) :
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
