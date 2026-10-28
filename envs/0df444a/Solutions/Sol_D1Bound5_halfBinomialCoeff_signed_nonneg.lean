-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_signed_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:24.088903+00:00
-- url     : https://prove2.me/submissions/48f653d5-5b61-4f62-94b5-e56e2798de67

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





/-- The coefficients have alternating signs from degree one onward. -/
theorem _root_.solution (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ n * halfBinomialCoeff (n + 1) := by
  induction n with
  | zero =>
      norm_num [halfBinomialCoeff, Ring.choose_one_right]
  | succ n ih =>
      have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hrec :
          ((n : ℝ) + 2) * halfBinomialCoeff (n + 2) =
            ((1 / 2 : ℝ) - ((n : ℝ) + 1)) * halfBinomialCoeff (n + 1) := by
        convert halfBinomialCoeff_recurrence (n + 1) using 1 <;>
          simp only [Nat.cast_add, Nat.cast_one] <;> ring
      have hsolve :
          halfBinomialCoeff (n + 2) =
          (((1 / 2 : ℝ) - (n + 1)) * halfBinomialCoeff (n + 1)) / (n + 2) := by
        apply (eq_div_iff (ne_of_gt hn)).2
        rw [mul_comm]
        exact hrec
      have hfactor : 0 ≤ ((n + 1 : ℝ) - (1 / 2 : ℝ)) / (n + 2) := by
        apply div_nonneg
        · have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          linarith
        · exact le_of_lt hn
      rw [pow_succ, hsolve]
      have heq :
          (-1 : ℝ) ^ n * -1 *
              ((((1 / 2 : ℝ) - (n + 1)) * halfBinomialCoeff (n + 1)) / (n + 2)) =
          ((-1 : ℝ) ^ n * halfBinomialCoeff (n + 1)) *
              (((n + 1 : ℝ) - (1 / 2 : ℝ)) / (n + 2)) := by ring
      rw [heq]
      exact mul_nonneg ih hfactor











end D1Bound5
end
