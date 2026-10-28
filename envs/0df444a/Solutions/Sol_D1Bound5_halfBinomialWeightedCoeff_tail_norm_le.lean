-- Prove2me | solution 1 for D1Bound5.halfBinomialWeightedCoeff_tail_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:27:50.114766+00:00
-- url     : https://prove2.me/submissions/d48c4032-932d-4ebb-901a-8357f627ace7

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_abs_antitone
import Theorems.Thm_D1Bound5_halfBinomialWeightedCoeff_norm_le

section
open Finset

namespace D1Bound5





/-- The monotonicity of the half-binomial coefficients gives one fixed
envelope for every degree at least m+1, when m is positive. -/
theorem _root_.solution
    (x y : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hx : ‖x‖ ≤ t) (hy : ‖y‖ ≤ t)
    (m n : ℕ) (hm : 1 ≤ m) (hn : m + 1 ≤ n) :
    ‖halfBinomialWeightedCoeff x y n‖ ≤
      4 * |halfBinomialCoeff (m + 1)| * t ^ n := by
  have hn2 : 2 ≤ n := by omega
  have hb : |halfBinomialCoeff n| ≤ |halfBinomialCoeff (m + 1)| :=
    halfBinomialCoeff_abs_antitone (by omega) hn
  calc
    ‖halfBinomialWeightedCoeff x y n‖ ≤
      4 * |halfBinomialCoeff n| * t ^ n :=
        halfBinomialWeightedCoeff_norm_le x y t ht hx hy n hn2
    _ ≤ 4 * |halfBinomialCoeff (m + 1)| * t ^ n := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb (by norm_num))
          (pow_nonneg ht _)



end D1Bound5
end
