-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_abs_next_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:23.465293+00:00
-- url     : https://prove2.me/submissions/93c3b198-2952-40ef-a748-a1f550edd312

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_recurrence

section
open Finset

namespace D1Bound5







/-- Absolute coefficients weakly decrease from degree one onward. -/
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    |halfBinomialCoeff (n + 1)| ≤ |halfBinomialCoeff n| := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsign : (1 / 2 : ℝ) - n ≤ 0 := by linarith
  have hnum : |(1 / 2 : ℝ) - n| ≤ (n + 1 : ℝ) := by
    rw [abs_of_nonpos hsign]
    linarith
  have hre := congrArg abs (halfBinomialCoeff_recurrence n)
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ))] at hre
  have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmul :
      ((n : ℝ) + 1) * |halfBinomialCoeff (n + 1)| ≤
        ((n : ℝ) + 1) * |halfBinomialCoeff n| := by
    rw [hre]
    exact mul_le_mul_of_nonneg_right hnum (abs_nonneg _)
  exact (mul_le_mul_iff_of_pos_left hp).mp hmul









end D1Bound5
end
