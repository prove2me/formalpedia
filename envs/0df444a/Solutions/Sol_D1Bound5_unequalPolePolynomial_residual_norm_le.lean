-- Prove2me | solution 1 for D1Bound5.unequalPolePolynomial_residual_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:48.012174+00:00
-- url     : https://prove2.me/submissions/2ab96e21-362a-43be-ad30-a6c725462329

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
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettRepeatedHsymm_Definitions
import Definitions.Def_D1Bound5_UnequalPoleResidual_Definitions
import Theorems.Thm_D1Bound5_bennettLocalResidue_sum_X_pow_eq_hsymm
import Theorems.Thm_D1Bound5_bennettRepeatedNodes_card
import Theorems.Thm_D1Bound5_bennett_homogeneous_tail_summable_and_norm_le
import Theorems.Thm_D1Bound5_unequalPolePolynomial_residual_tail_hasSum

section
open Finset

namespace D1Bound5

variable {I : Type*} [Fintype I] [DecidableEq I]











/-- General multiplicity version of the proved Bennett residual estimate.
This is an actual bound on explicit polynomials, with no contour formula,
residual assumption or unverified finite coefficient assertion. -/
theorem _root_.solution
    (a : I → ℂ) (ha : Function.Injective a) (e : I → ℕ)
    (q : I) (k : ℕ) (he : ∀ j, e j ≤ k) (ν ρ : ℝ) (x : ℂ)
    (hs : (k : ℝ)+ν < ((∑ j,(e j+1))-1 : ℕ))
    (hρ0 : 0 ≤ ρ) (hρ : ∀ j, ‖a j‖ ≤ ρ) (hradius : ρ*‖x‖ < 1) :
    ‖∑ j, (unequalPolePolynomial a e k (ν : ℂ) j).eval x*
      (1+a j*x)^(ν : ℂ)‖ ≤
      |Ring.choose ((k : ℝ)+ν) ((∑ j,(e j+1))-1)| *
        ‖x‖^((∑ j,(e j+1))-1) /
          (1-ρ*‖x‖)^((((∑ j,(e j+1))-1 : ℕ) : ℝ)-((k : ℝ)+ν)) := by
  let D : ℕ := (∑ j,(e j+1))-1
  let A : BennettRepeatedNodes e → ℂ := fun j => a j.1
  letI : Nonempty (BennettRepeatedNodes e) := ⟨⟨q,0⟩⟩
  have htotal : 0 < ∑ j,(e j+1) := by
    have hh : e q+1 ≤ ∑ j,(e j+1) := Finset.single_le_sum (f := fun j : I => e j+1)
      (fun j _ => Nat.zero_le (e j+1)) (Finset.mem_univ q)
    omega
  have hcard : Fintype.card (BennettRepeatedNodes e) = D+1 := by
    rw [bennettRepeatedNodes_card]
    dsimp [D]
    omega
  have hA (j : BennettRepeatedNodes e) : ‖A j‖ ≤ ρ := hρ j.1
  have hmoment (t : ℕ) :
      (∑ j, bennettLocalResidue a e (Polynomial.X^(D+t)) j) =
      MvPolynomial.aeval A (MvPolynomial.hsymm (BennettRepeatedNodes e) ℂ t) :=
    bennettLocalResidue_sum_X_pow_eq_hsymm a ha e htotal t
  have hx (j : I) : ‖a j*x‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hρ j) (norm_nonneg x)).trans_lt hradius
  have htail := unequalPolePolynomial_residual_tail_hasSum a ha e k he (ν : ℂ) x hx
  change HasSum (fun t : ℕ =>
      (Ring.choose ((k : ℂ)+(ν : ℂ)) (D+t) *
        ∑ j, bennettLocalResidue a e (Polynomial.X^(D+t)) j)*x^(D+t)) _ at htail
  simp_rw [hmoment] at htail
  have hbound := bennett_homogeneous_tail_summable_and_norm_le A D
    ((k : ℝ)+ν) ρ x hcard hs hρ0 hA hradius
  rw [← htail.tsum_eq]
  simpa only [D, Complex.ofReal_add, Complex.ofReal_natCast] using hbound.2

end D1Bound5
end
