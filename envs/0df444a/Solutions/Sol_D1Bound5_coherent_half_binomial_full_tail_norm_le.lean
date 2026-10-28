-- Prove2me | solution 1 for D1Bound5.coherent_half_binomial_full_tail_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:47.509805+00:00
-- url     : https://prove2.me/submissions/ca4fbc10-7afb-4182-b79b-c410d20fcbf4

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_coherent_half_binomial_tail_summable_and_norm_le

section
open Finset Polynomial

namespace D1Bound5











/-- The full homogeneous tail is summable, and its difference from the
leading coefficient satisfies precisely the paper's sharp remainder
bound.  This is the `F_m - f_m` form of the existing positive-tail bound. -/
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ι → ℂ) (x y : ℂ) (m : ℕ) (ρ t : ℝ)
    (hm : 1 ≤ m) (hρ0 : 0 ≤ ρ) (ht : 0 ≤ t)
    (ha : ∀ i, ‖a i‖ ≤ ρ)
    (hx : ‖x‖ ≤ t) (hy : ‖y‖ ≤ t)
    (hradius : ρ * t < 1) :
    Summable (fun j : ℕ => halfBinomialWeightedCoeff x y (m + j) *
      MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ j)) ∧
    ‖(∑' j : ℕ, halfBinomialWeightedCoeff x y (m + j) *
      MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ j)) -
        halfBinomialWeightedCoeff x y m‖ ≤
      (4 * |halfBinomialCoeff (m + 1)|) * t ^ m *
        (1 / (1 - ρ * t) ^ Fintype.card ι - 1) := by
  have h := coherent_half_binomial_tail_summable_and_norm_le
    a x y m ρ t hm hρ0 ht ha hx hy hradius
  have hfull : Summable (fun j : ℕ => halfBinomialWeightedCoeff x y (m + j) *
      MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ j)) :=
    (summable_nat_add_iff 1).mp h.1
  refine ⟨hfull, ?_⟩
  have hsplit := hfull.tsum_eq_zero_add
  simp only [Nat.add_zero, MvPolynomial.hsymm_zero, map_one, mul_one] at hsplit
  rw [hsplit, add_sub_cancel_left]
  exact h.2

end D1Bound5




open Finset

namespace D1Bound5



end D1Bound5




open Finset

namespace D1Bound5





end D1Bound5




namespace D1Bound5









end D1Bound5
end
