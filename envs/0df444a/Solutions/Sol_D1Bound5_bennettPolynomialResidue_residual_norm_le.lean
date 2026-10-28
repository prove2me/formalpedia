-- Prove2me | solution 1 for D1Bound5.bennettPolynomialResidue_residual_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:28:55.306454+00:00
-- url     : https://prove2.me/submissions/8e48aad7-079d-4af9-bc24-84e87fe79065

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
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettRepeatedHsymm_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Theorems.Thm_D1Bound5_bennettLocalResidue_sum_X_pow_eq_hsymm
import Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_tail_hasSum
import Theorems.Thm_D1Bound5_bennettRepeatedNodes_card
import Theorems.Thm_D1Bound5_bennett_homogeneous_tail_summable_and_norm_le

section
open Finset

namespace D1Bound5

/-- An unconditional analytic bound for the actual arbitrary-order Bennett
residual. The proof joins actual polynomial evaluation, exact residue moments,
the repeated-node homogeneous identity, and the convergent binomial majorant.
No contour formula or residual-bound hypothesis occurs in the statement. -/
theorem _root_.solution
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℂ) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν ρ : ℝ) (x : ℂ) (i : I)
    (hs : (k : ℝ) + ν < (Fintype.card I * k : ℕ))
    (hρ0 : 0 ≤ ρ) (hρ : ∀ j, ‖a j‖ ≤ ρ) (hradius : ρ * ‖x‖ < 1) :
    ‖∑ j, (bennettPolynomialResidue univ a k (ν : ℂ) i j).eval x *
        (1 + a j * x) ^ (ν : ℂ)‖ ≤
      |Ring.choose ((k : ℝ) + ν) (Fintype.card I * k)| *
        ‖x‖ ^ (Fintype.card I * k) /
          (1 - ρ * ‖x‖) ^ (((Fintype.card I * k : ℕ) : ℝ) - ((k : ℝ) + ν)) := by
  let e : I → ℕ := fun l => k + (if i = l then 1 else 0) - 1
  let A : BennettRepeatedNodes e → ℂ := fun j => a j.1
  letI : Nonempty (BennettRepeatedNodes e) := ⟨⟨i, 0⟩⟩
  have he (j : I) : e j + 1 = k + (if i = j then 1 else 0) := by
    dsimp [e]
    split_ifs <;> omega
  have htotal : (∑ j, (e j + 1)) = Fintype.card I * k + 1 := by
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp
  have hd : 0 < ∑ j, (e j + 1) := by rw [htotal]; omega
  have hcard : Fintype.card (BennettRepeatedNodes e) = Fintype.card I * k + 1 := by
    rw [bennettRepeatedNodes_card, htotal]
  have hA (j : BennettRepeatedNodes e) : ‖A j‖ ≤ ρ := hρ j.1
  have hmoment (t : ℕ) :
      (∑ j, bennettLocalResidue a e
        (Polynomial.X ^ (Fintype.card I * k + t)) j) =
      MvPolynomial.aeval A (MvPolynomial.hsymm (BennettRepeatedNodes e) ℂ t) := by
    simpa only [htotal, Nat.add_sub_cancel] using
      bennettLocalResidue_sum_X_pow_eq_hsymm a ha e hd t
  have hx (j : I) : ‖a j * x‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hρ j) (norm_nonneg x)).trans_lt hradius
  have htail := bennettPolynomialResidue_residual_tail_hasSum a ha k hk (ν : ℂ) x i hx
  change HasSum (fun t : ℕ =>
      (Ring.choose ((k : ℂ) + (ν : ℂ)) (Fintype.card I * k + t) *
        ∑ j, bennettLocalResidue a e
          (Polynomial.X ^ (Fintype.card I * k + t)) j) *
            x ^ (Fintype.card I * k + t)) _ at htail
  simp_rw [hmoment] at htail
  have hbound := bennett_homogeneous_tail_summable_and_norm_le
    A (Fintype.card I * k) ((k : ℝ) + ν) ρ x hcard hs hρ0 hA hradius
  rw [← htail.tsum_eq]
  simpa only [Complex.ofReal_add, Complex.ofReal_natCast] using hbound.2



end D1Bound5
end
