-- Prove2me | solution 1 for Diaz.coeff_transfer_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:31:18.979737+00:00
-- url     : https://prove2.me/submissions/ed698637-696f-43db-9f7d-7477ee2d7c82

import Mathlib

open ComplexConjugate

theorem solution {K : Subfield ℂ} {m n : Type*} [Fintype m] [Fintype n]
    (Φ : ℂ →+* ℂ) (hK : ∀ a ∈ K, Φ a = a)
    (M : Matrix m n ℂ) (w : m → ℂ) (v : n → ℂ)
    (hw : ∀ i, w i ∈ K) (hv : ∀ j, v j ∈ K) :
    Φ (∑ i, ∑ j, w i * M i j * v j) = ∑ i, ∑ j, w i * Φ (M i j) * v j ∧
      ((∑ i, ∑ j, w i * M i j * v j) = 0 ↔ (∑ i, ∑ j, w i * Φ (M i j) * v j) = 0) := by
  have key : Φ (∑ i, ∑ j, w i * M i j * v j) = ∑ i, ∑ j, w i * Φ (M i j) * v j := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hK _ (hw i), hK _ (hv j)]
  refine ⟨key, ?_, ?_⟩
  · intro h0
    rw [← key, h0, map_zero]
  · intro h0
    refine Φ.injective ?_
    rw [key, h0, map_zero]
