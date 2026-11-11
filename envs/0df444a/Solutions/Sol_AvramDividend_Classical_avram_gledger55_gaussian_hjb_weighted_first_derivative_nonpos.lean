-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger55_gaussian_hjb_weighted_first_derivative_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:02:57.299314+00:00
-- url     : https://prove2.me/submissions/5cf4a13e-1dc7-4d3f-8ad1-a18bd326f482

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- The two characteristic roots factor the Gaussian HJB supersolution
    into a positive integrating factor and a nonpositive first derivative. -/
theorem solution
    (a b q r l : ℝ) (ha : 0 < a)
    (hlin : b = -a * (r + l)) (hprod : q = -a * r * l)
    (w : ℝ → ℝ)
    (hsmooth : ∀ y : ℝ, 0 < y →
      HasDerivAt w (deriv w y) y ∧
        HasDerivAt (deriv w) (iteratedDeriv 2 w y) y)
    (hode : ∀ y : ℝ, 0 < y →
      a * iteratedDeriv 2 w y + b * deriv w y - q * w y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      deriv (fun z => Real.exp (-(r * z)) * (deriv w z - l * w z)) y ≤ 0 := by
  intro y hy
  obtain ⟨hw, hw'⟩ := hsmooth y hy
  have hlinear : HasDerivAt (fun z : ℝ => -(r * z)) (-r) y := by
    simpa only [id_eq, mul_one, neg_mul] using (hasDerivAt_id y).const_mul (-r)
  have he : HasDerivAt (fun z : ℝ => Real.exp (-(r * z)))
      (-r * Real.exp (-(r * y))) y := by
    simpa only [mul_comm] using hlinear.exp
  have hsub : HasDerivAt (fun z => deriv w z - l * w z)
      (iteratedDeriv 2 w y - l * deriv w y) y := by
    exact hw'.sub (hw.const_mul l)
  have hd := (he.mul hsub).deriv
  have hfactor :
      a * (iteratedDeriv 2 w y - (r + l) * deriv w y + r * l * w y) =
        a * iteratedDeriv 2 w y + b * deriv w y - q * w y := by
    rw [hlin, hprod]
    ring
  have hnonpos :
      iteratedDeriv 2 w y - (r + l) * deriv w y + r * l * w y ≤ 0 := by
    have hmul : a * (iteratedDeriv 2 w y -
        (r + l) * deriv w y + r * l * w y) ≤ 0 := by
      rw [hfactor]
      exact hode y hy
    by_contra hn
    have hp : 0 < iteratedDeriv 2 w y -
        (r + l) * deriv w y + r * l * w y := lt_of_not_ge hn
    exact (not_lt_of_ge hmul) (mul_pos ha hp)
  have hexp :
      Real.exp (-(r * y)) *
          (iteratedDeriv 2 w y - (r + l) * deriv w y + r * l * w y) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hnonpos
  calc
    deriv (fun z => Real.exp (-(r * z)) * (deriv w z - l * w z)) y =
        (-r * Real.exp (-(r * y))) * (deriv w y - l * w y) +
          Real.exp (-(r * y)) * (iteratedDeriv 2 w y - l * deriv w y) := hd
    _ = Real.exp (-(r * y)) *
        (iteratedDeriv 2 w y - (r + l) * deriv w y + r * l * w y) := by ring
    _ ≤ 0 := hexp
