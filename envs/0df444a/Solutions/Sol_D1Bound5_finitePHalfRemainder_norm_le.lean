-- Prove2me | solution 1 for D1Bound5.finitePHalfRemainder_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:44:42.970994+00:00
-- url     : https://prove2.me/submissions/84d4a158-9aa4-43b1-927c-5f609f79fed0

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_finiteP_half_coefficients
import Theorems.Thm_D1Bound5_halfBinomialCoeff_abs_antitone
import Theorems.Thm_D1Bound5_halfBinomialCoeff_hasSum_cpow

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three



/-- Degree-six tail estimate for the actual principal half power. -/
theorem _root_.solution (n : ℕ) (z : ℂ)
    (hn : 6 ≤ n) (hz : ‖z‖ < 1) :
    ‖finiteQHalfRemainder n z‖ ≤ (21/1024 : ℝ)*‖z‖^n/(1-‖z‖) := by
  have hs := halfBinomialCoeff_hasSum_cpow z hz
  have htail : HasSum (fun j : ℕ => (halfBinomialCoeff (j+n) : ℂ)*z^(j+n))
      (finiteQHalfRemainder n z) := (hasSum_nat_add_iff' n).2 hs
  have hr : ‖(‖z‖ : ℝ)‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] using hz
  have hgeom := (hasSum_geometric_of_norm_lt_one hr).mul_left
    ((21/1024 : ℝ)*‖z‖^n)
  have hterm (j : ℕ) :
      ‖(halfBinomialCoeff (j+n) : ℂ)*z^(j+n)‖ ≤
        ((21/1024 : ℝ)*‖z‖^n)*‖z‖^j := by
    have hb : |halfBinomialCoeff (j+n)| ≤ (21/1024 : ℝ) := by
      have h := halfBinomialCoeff_abs_antitone (j := 6) (k := j+n)
        (by decide) (by omega)
      rw [finiteP_half_coefficients.2.1] at h
      norm_num at h ⊢
      exact h
    calc
      _ = |halfBinomialCoeff (j+n)| *‖z‖^(j+n) := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (21/1024 : ℝ)*‖z‖^(j+n) :=
        mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg z) _)
      _ = _ := by rw [pow_add]; ring
  have hnorm : Summable (fun j : ℕ => ‖(halfBinomialCoeff (j+n) : ℂ)*z^(j+n)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hgeom.summable
  calc
    _ = ‖∑' j : ℕ, (halfBinomialCoeff (j+n) : ℂ)*z^(j+n)‖ := by rw [htail.tsum_eq]
    _ ≤ ∑' j : ℕ, ‖(halfBinomialCoeff (j+n) : ℂ)*z^(j+n)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ, ((21/1024 : ℝ)*‖z‖^n)*‖z‖^j :=
      hnorm.tsum_le_tsum hterm hgeom.summable
    _ = (21/1024 : ℝ)*‖z‖^n/(1-‖z‖) := by rw [hgeom.tsum_eq]; rfl































end D1Bound5
end
