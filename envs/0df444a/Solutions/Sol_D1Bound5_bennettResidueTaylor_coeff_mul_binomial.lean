-- Prove2me | solution 1 for D1Bound5.bennettResidueTaylor_coeff_mul_binomial
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:10:59.221431+00:00
-- url     : https://prove2.me/submissions/2f05122e-21bf-4989-ab72-80053023e870

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Theorems.Thm_D1Bound5_bennettBinomial_coefficient_transfer

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

/-- Multiplying the actual local residue polynomial by its binomial series
transfers each coefficient to the residue of a polynomial monomial. -/
theorem _root_.solution (k t r : ℕ) (ht : t ≤ k)
    (ν a : F) (B : PowerSeries F) :
    PowerSeries.coeff r
      ((bennettResidueTaylor k t ν a B : PowerSeries F) *
        PowerSeries.rescale a (PowerSeries.binomialSeries F ν)) =
      Ring.choose ((k : F) + ν) r *
        PowerSeries.coeff t (((PowerSeries.C a + PowerSeries.X) ^ r) * B) := by
  have hp : (bennettResidueTaylor k t ν a B : PowerSeries F) =
      ∑ hu ∈ Finset.antidiagonal t,
        PowerSeries.C (Ring.choose ((k : F) + ν) hu.1 * PowerSeries.coeff hu.2 B) *
          (PowerSeries.X ^ hu.1 *
            (1 + PowerSeries.C a * PowerSeries.X) ^ (k - hu.1)) := by
    change Polynomial.coeToPowerSeries.ringHom (bennettResidueTaylor k t ν a B) = _
    unfold bennettResidueTaylor
    simp only [map_sum, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
      Polynomial.coe_X, Polynomial.coe_add, Polynomial.coe_one]
  rw [hp, Finset.sum_mul, map_sum]
  calc
    _ = ∑ hu ∈ Finset.antidiagonal t,
        Ring.choose ((k : F) + ν) r *
          (PowerSeries.coeff hu.1 ((PowerSeries.C a + PowerSeries.X) ^ r) *
            PowerSeries.coeff hu.2 B) := by
      apply Finset.sum_congr rfl
      intro hu hhu
      have hsum := Finset.mem_antidiagonal.mp hhu
      have hh : hu.1 ≤ k := by omega
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      calc
        _ = PowerSeries.coeff hu.2 B *
            (Ring.choose ((k : F) + ν) hu.1 *
              PowerSeries.coeff r
                ((PowerSeries.X ^ hu.1 *
                  (1 + PowerSeries.C a * PowerSeries.X) ^ (k - hu.1)) *
                    PowerSeries.rescale a (PowerSeries.binomialSeries F ν))) := by ring
        _ = _ := by
          rw [bennettBinomial_coefficient_transfer k hu.1 r hh ν a]
          ring
    _ = _ := by rw [PowerSeries.coeff_mul, Finset.mul_sum]

section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]











end Nodes

end D1Bound5
end
