-- Prove2me | solution 1 for D1Bound5.coherent_half_binomial_tail_summable_and_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:27:42.308036+00:00
-- url     : https://prove2.me/submissions/7137cc1a-7536-41e4-9348-45b5110e1e6c

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
import Theorems.Thm_D1Bound5_coherent_weighted_remainder_summable_and_norm_le
import Theorems.Thm_D1Bound5_halfBinomialWeightedCoeff_tail_norm_le

section
open Finset

namespace D1Bound5







/-- The actual complex half-binomial convolution satisfies the complete
weighted-homogeneous tail bound. The coefficient envelope is proved here,
rather than inserted as an independent hypothesis. -/
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ι → ℂ) (x y : ℂ) (m : ℕ) (ρ t : ℝ)
    (hm : 1 ≤ m) (hρ0 : 0 ≤ ρ) (ht : 0 ≤ t)
    (ha : ∀ i, ‖a i‖ ≤ ρ)
    (hx : ‖x‖ ≤ t) (hy : ‖y‖ ≤ t)
    (hradius : ρ * t < 1) :
    Summable (fun j : ℕ => halfBinomialWeightedCoeff x y (m + (j + 1)) *
      MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))) ∧
    ‖∑' j : ℕ, halfBinomialWeightedCoeff x y (m + (j + 1)) *
      MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))‖ ≤
      (4 * |halfBinomialCoeff (m + 1)|) * t ^ m *
        (1 / (1 - ρ * t) ^ Fintype.card ι - 1) := by
  have hcoeff (j : ℕ) :
      ‖halfBinomialWeightedCoeff x y (m + (j + 1))‖ ≤
        (4 * |halfBinomialCoeff (m + 1)|) * t ^ (m + (j + 1)) := by
    exact halfBinomialWeightedCoeff_tail_norm_le
      x y t ht hx hy m (m + (j + 1)) hm (by omega)
  exact coherent_weighted_remainder_summable_and_norm_le
    a (halfBinomialWeightedCoeff x y) m
      (4 * |halfBinomialCoeff (m + 1)|) ρ t
      (mul_nonneg (by norm_num) (abs_nonneg _)) hρ0 ht ha hradius hcoeff

end D1Bound5
end
