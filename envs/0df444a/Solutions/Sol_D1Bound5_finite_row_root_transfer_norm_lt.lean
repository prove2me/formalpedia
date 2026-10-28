-- Prove2me | solution 1 for D1Bound5.finite_row_root_transfer_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:40:14.451987+00:00
-- url     : https://prove2.me/submissions/a14f37cf-670e-4124-8000-fcf87b18b71f

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5

/-- An intermediate analytic transfer for finite integral rows. It states
only the triangle-inequality step: each application must provide its actual
coefficients, residual estimate, and signed root errors. -/
theorem _root_.solution
    {I : Type*} [Fintype I] (q0 z : ℂ) (a p theta s : I → ℂ)
    (ha : ∀ j, a j ≠ 0) (hz : z ≠ 0) (E H R : ℝ) (hE : 0 ≤ E)
    (herr : ∀ j, ‖theta j-s j/(a j*z)‖ ≤ E/(‖a j‖*‖z‖^2))
    (hheight : (∑ j, ‖p j‖) ≤ H)
    (hres : ‖q0+∑ j, a j*p j*theta j‖ < R) :
    ‖q0*z+∑ j, p j*s j‖ < R*‖z‖+E*H/‖z‖ := by
  classical
  have hZ : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hsum :
      (∑ j, (a j*p j*z)*(theta j-s j/(a j*z))) =
        z*(∑ j, a j*p j*theta j)-(∑ j, p j*s j) := by
    calc
      _ = ∑ j, (z*(a j*p j*theta j)-p j*s j) := by
        apply Finset.sum_congr rfl
        intro j _
        field_simp [ha j, hz]
        <;> ring
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have hform : q0*z+∑ j, p j*s j =
      z*(q0+∑ j, a j*p j*theta j)-
        ∑ j, (a j*p j*z)*(theta j-s j/(a j*z)) := by
    rw [hsum]
    ring
  have hterm (j : I) :
      ‖(a j*p j*z)*(theta j-s j/(a j*z))‖ ≤ (E/‖z‖)*‖p j‖ := by
    rw [norm_mul]
    calc
      _ ≤ ‖a j*p j*z‖*(E/(‖a j‖*‖z‖^2)) :=
        mul_le_mul_of_nonneg_left (herr j) (norm_nonneg _)
      _ = _ := by
        simp only [norm_mul]
        field_simp [norm_ne_zero_iff.mpr (ha j), norm_ne_zero_iff.mpr hz]
        <;> ring
  have herrsum :
      ‖∑ j, (a j*p j*z)*(theta j-s j/(a j*z))‖ ≤ E*H/‖z‖ := by
    calc
      _ ≤ ∑ j, ‖(a j*p j*z)*(theta j-s j/(a j*z))‖ := norm_sum_le _ _
      _ ≤ ∑ j, (E/‖z‖)*‖p j‖ := Finset.sum_le_sum (fun j _ => hterm j)
      _ = (E/‖z‖)*(∑ j, ‖p j‖) := by rw [Finset.mul_sum]
      _ ≤ (E/‖z‖)*H := mul_le_mul_of_nonneg_left hheight (div_nonneg hE hZ.le)
      _ = _ := by ring
  calc
    _ ≤ ‖z*(q0+∑ j, a j*p j*theta j)‖+
        ‖∑ j, (a j*p j*z)*(theta j-s j/(a j*z))‖ := by
      rw [hform]
      exact norm_sub_le _ _
    _ ≤ ‖z*(q0+∑ j, a j*p j*theta j)‖+E*H/‖z‖ := add_le_add le_rfl herrsum
    _ < R*‖z‖+E*H/‖z‖ := by
      rw [norm_mul]
      have h := mul_lt_mul_of_pos_left hres hZ
      nlinarith only [h]

end D1Bound5
end
