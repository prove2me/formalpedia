-- Prove2me | solution 1 for CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport.mem_directional_support_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:47:45.087161+00:00
-- url     : https://prove2.me/submissions/d8eb483a-a794-4061-a470-05f7e7373402

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Positivity

namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
section


set_option autoImplicit false

/-!
Support calculations for a nonnegative directional derivative. Its coefficients
are nonnegative, and its support consists precisely of exponents obtained by
removing a unit in a direction with positive weight. The exchange condition
is preserved by a finite exchange argument on these lifted exponents.
-/

namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport

open scoped BigOperators

/-- INTERNAL: Nonnegative directional differentiation has no coefficient cancellation.
TEXLINE: main.tex:340-348 -/
theorem directional_coeff_nonnegative {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (hp : ∀ m, 0 ≤ p.coeff m)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) (m : σ →₀ ℕ) :
    0 ≤ (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p).coeff m := by
  classical
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_nonneg
  intro s _
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_pderiv]
  exact mul_nonneg (hd s) (mul_nonneg (hp _) (by positivity))





end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed directional support exchange by lifting support witnesses and using at most three original-support exchanges; no new proof obligations.
-/

end
set_option autoImplicit false

/-!
Support calculations for a nonnegative directional derivative. Its coefficients
are nonnegative, and its support consists precisely of exponents obtained by
removing a unit in a direction with positive weight. The exchange condition
is preserved by a finite exchange argument on these lifted exponents.
-/

namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport

open scoped BigOperators

/-- INTERNAL: The support of a directional derivative is a weighted union of
unit deletions, with no cancellation because all coefficients are nonnegative.
TEXLINE: main.tex:340-348 -/
theorem solution {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (hp : ∀ m, 0 ≤ p.coeff m)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) (m : σ →₀ ℕ) :
    m ∈ (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p).support ↔
      ∃ s, 0 < d s ∧ m + Finsupp.single s 1 ∈ p.support := by
  classical
  rw [MvPolynomial.mem_support_iff]
  have hnonneg := directional_coeff_nonnegative p hp d hd m
  rw [ne_comm, ne_iff_lt_iff_le.mpr hnonneg]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_pderiv]
  rw [Finset.sum_pos_iff_of_nonneg (fun s _ =>
    mul_nonneg (hd s) (mul_nonneg (hp _) (by positivity)))]
  simp only [Finset.mem_univ, true_and]
  apply exists_congr
  intro s
  have hnat : (0 : ℚ) < (m s : ℚ) + 1 := by positivity
  rw [← mul_assoc, mul_pos_iff_of_pos_right hnat]
  rw [mul_pos_iff]
  have hdnot : ¬ d s < 0 := not_lt.mpr (hd s)
  simp only [hdnot, false_and, or_false, MvPolynomial.mem_support_iff]
  rw [ne_comm, ne_iff_lt_iff_le.mpr (hp _)]
