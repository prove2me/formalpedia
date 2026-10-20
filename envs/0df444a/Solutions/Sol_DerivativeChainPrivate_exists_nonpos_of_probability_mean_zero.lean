-- Prove2me | solution 1 for DerivativeChainPrivate.exists_nonpos_of_probability_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:46:00.377349+00:00
-- url     : https://prove2.me/submissions/5d6d823d-3d2a-44da-8ec9-627c0ab96e6f


import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false

namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate in
theorem solution {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hzero : ∑ i, p i * f i = 0) :
    ∃ i, f i ≤ 0 := by
  classical
  have hs : (Finset.univ : Finset ι).Nonempty := by
    exact Finset.nonempty_of_sum_ne_zero
      (show (∑ i, p i) ≠ 0 by rw [hsum]; exact one_ne_zero)
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ f hs
  have havg : f i ≤ ∑ j, p j * f j := by
    calc
      f i = ∑ j, p j * f i := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ j, p j * f j := Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hmin j hj) (hp j)
  exact ⟨i, hzero ▸ havg⟩
