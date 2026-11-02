-- Prove2me | solution 1 for DirectFidelity.State.prob_normalized
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:34:45.759807+00:00
-- url     : https://prove2.me/submissions/31683ae4-c3fd-4a28-a7c5-89b78a3f249a

import Mathlib
import Definitions.Def_DirectFidelity_State_Setting
import Theorems.Thm_DirectFidelity_State_eq_2
set_option autoImplicit false

open DirectFidelity.State

theorem solution (n : ℕ) (ρ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ) :
    ∑ k : P n, prob ρ k = ((ρ * ρ).trace).re ∧ ((ρ * ρ).trace).re = 1 := by
  rcases hρ with ⟨ψ, hψ, rfl⟩
  have hHerm : (Matrix.vecMulVec ψ (star ψ)).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  have hdot : ∑ x : Q n, star (ψ x) * ψ x = 1 := by
    simpa [dotProduct, Pi.star_apply] using hψ
  have h_idem : Matrix.vecMulVec ψ (star ψ) * Matrix.vecMulVec ψ (star ψ) =
      Matrix.vecMulVec ψ (star ψ) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    have hsum : ∑ x : Q n, ψ i * star (ψ x) * (ψ x * star (ψ j)) =
        (ψ i * star (ψ j)) * ∑ x : Q n, star (ψ x) * ψ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [hsum, hdot, mul_one]
  have h_tr : (Matrix.vecMulVec ψ (star ψ)).trace = 1 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    have hsum : ∑ x : Q n, ψ x * star (ψ x) = ∑ x : Q n, star (ψ x) * ψ x :=
      Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [hsum, hdot]
  refine ⟨?_, ?_⟩
  · rw [DirectFidelity.State.eq_2 n _ _ hHerm hHerm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [prob, sq]
  · rw [h_idem, h_tr, Complex.one_re]
