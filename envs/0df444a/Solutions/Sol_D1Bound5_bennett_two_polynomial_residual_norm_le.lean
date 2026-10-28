-- Prove2me | solution 1 for D1Bound5.bennett_two_polynomial_residual_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:46:07.694315+00:00
-- url     : https://prove2.me/submissions/2e6e6a14-952d-4e79-ac9d-44195e9e8025

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_norm_le
import Theorems.Thm_D1Bound5_bennett_two_residual_choose_abs_Gamma

section
open Finset

namespace D1Bound5



/-- Exact two-anchor analytic residual estimate, including the manuscript's
Gamma factor and exponent 2k-1/2. This concerns the actual P-matrix. -/
theorem _root_.solution
    (a : Fin 3 → ℂ) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ρ : ℝ) (x : ℂ) (i : Fin 3)
    (hρ0 : 0 ≤ ρ) (hρ : ∀ j, ‖a j‖ ≤ ρ) (hradius : ρ * ‖x‖ < 1) :
    ‖∑ j, (bennettPolynomialResidue univ a k (1 / 2 : ℂ) i j).eval x *
        (1 + a j * x) ^ (1 / 2 : ℂ)‖ ≤
      (Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma (2 * (k : ℝ) - 1 / 2) /
        (Real.pi * Real.Gamma (3 * (k : ℝ) + 1))) * ‖x‖ ^ (3 * k) /
          (1 - ρ * ‖x‖) ^ (2 * (k : ℝ) - 1 / 2) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : (k : ℝ) + 1 / 2 < (Fintype.card (Fin 3) * k : ℕ) := by
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have hexp : ((3 * k : ℕ) : ℝ) - ((k : ℝ) + 1 / 2) =
      2 * (k : ℝ) - 1 / 2 := by push_cast; ring
  have h := bennettPolynomialResidue_residual_norm_le a ha k hk (1 / 2) ρ x i
    hs hρ0 hρ hradius
  simpa only [Fintype.card_fin, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, hexp, bennett_two_residual_choose_abs_Gamma k hk] using h

end D1Bound5
end
