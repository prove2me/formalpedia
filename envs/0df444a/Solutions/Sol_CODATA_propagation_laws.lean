-- Prove2me | solution 1 for CODATA.propagation_laws
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:08:23.180801+00:00
-- url     : https://prove2.me/submissions/92187ea6-3df4-4dfc-b757-eaf0ae41e026

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values
/-!
# The laws of propagation of relative uncertainty

The recommended values of the 2022 CODATA report are obtained from
the adjusted constants by propagating their uncertainties and
covariances. This milestone verifies the algebraic skeleton of that
propagation law for relative uncertainties, in the form recorded in
`Def_CODATA_uncert`: the correlation coefficient of an entry with
itself is one; the relative variance of a single component of the
value vector is the square of its relative uncertainty; the relative
variance scales quadratically in the sensitivity vector; and for
uncorrelated inputs the relative variances add. This milestone is
proved on the way to the goal theorem
`CODATA.codata_self_consistent`.
-/

open CODATA

/-- Let V be a covariance matrix with positive diagonal entries. Every
diagonal correlation coefficient is one; the relative variance of the
linear combination concentrated at a single component k with
sensitivity minus one is the square of the relative uncertainty of
that component; the relative variance scales by the square of a scalar
multiple of the sensitivity vector; and when all off-diagonal
covariances vanish, the relative variance of any linear combination is
the sum of the squared relative uncertainties weighted by the squared
sensitivities. -/
theorem solution {N : ℕ} (V : Matrix (Fin N) (Fin N) ℝ)
    (hV : ∀ k, 0 < V k k) :
    (∀ k, corr V k k = 1) ∧
      (∀ k (u x : Fin N → ℝ),
        relVar V u x (fun j => if j = k then -1 else 0)
          = (u k / abs (x k))^2) ∧
      (∀ c (p u x : Fin N → ℝ),
        relVar V u x (fun i => c * p i) = c * c * relVar V u x p) ∧
      ((∀ k l, k ≠ l → V k l = 0) →
        ∀ (p u x : Fin N → ℝ),
          relVar V u x p
            = ∑ k, p k * p k * (u k / abs (x k)) * (u k / abs (x k))) := by
  have hc : ∀ k, corr V k k = 1 := by
    intro k
    have := hV k
    simp only [corr]
    rw [Real.sqrt_mul_self this.le, div_self this.ne']
  refine ⟨hc, ?_, ?_, ?_⟩
  · intro k u x
    simp only [relVar]
    rw [Finset.sum_eq_single k, Finset.sum_eq_single k]
    · simp [hc k]; ring
    · intro b _ hb; simp [hb]
    · simp
    · intro b _ hb; apply Finset.sum_eq_zero; intro l _; simp [hb]
    · simp
  · intro c p u x
    simp only [relVar, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; ring
  · intro hoff p u x
    simp only [relVar]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_eq_single k]
    · rw [hc k]; ring
    · intro b _ hb
      have : corr V k b = 0 := by simp [corr, hoff k b (Ne.symm hb)]
      rw [this]; ring
    · simp


