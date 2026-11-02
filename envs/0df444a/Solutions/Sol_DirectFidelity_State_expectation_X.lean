-- Prove2me | solution 1 for DirectFidelity.State.expectation_X
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:35:12.76292+00:00
-- url     : https://prove2.me/submissions/731e3246-e401-417b-8161-56ec11511b48

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting
import Theorems.Thm_DirectFidelity_State_eq_2
open scoped ComplexOrder
set_option autoImplicit false

open DirectFidelity.State

theorem solution (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) :
    ∑ k : P n, prob ρ k * X ρ σ k = ((ρ * σ).trace).re := by
  rcases hρ with ⟨ψ, _, rfl⟩
  have hHerm : (Matrix.vecMulVec ψ (star ψ)).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  rw [DirectFidelity.State.eq_2 n _ σ hHerm hσ.1.isHermitian]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : chi (Matrix.vecMulVec ψ (star ψ)) k = 0
  · simp [prob, X, hk]
  · simp [prob, X, sq, mul_assoc, mul_div_cancel₀ _ hk]
