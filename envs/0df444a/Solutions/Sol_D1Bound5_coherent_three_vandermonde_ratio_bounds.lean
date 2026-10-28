-- Prove2me | solution 1 for D1Bound5.coherent_three_vandermonde_ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:27:11.03812+00:00
-- url     : https://prove2.me/submissions/49d3ef1f-aa90-4bdd-bf4f-6f4b052aeb82

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
open Finset

namespace D1Bound5

/-- The normalized Vandermonde factor in the retained estimate is
positive and at most eight for ordered nonzero distinct anchors. -/
theorem _root_.solution
    (a : Fin 3 → ℂ) (hinj : Function.Injective a)
    (hA : 0 < ‖a 0‖) (hAB : ‖a 0‖ ≤ ‖a 1‖) (hBS : ‖a 1‖ ≤ ‖a 2‖) :
    0 < ‖coherentVandermonde3 a‖/(‖a 1‖*‖a 2‖^2) ∧
      ‖coherentVandermonde3 a‖/(‖a 1‖*‖a 2‖^2) ≤ 8 := by
  have hB : 0 < ‖a 1‖ := hA.trans_le hAB
  have hS : 0 < ‖a 2‖ := hB.trans_le hBS
  have hDelta : coherentVandermonde3 a ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr (hinj.ne (by decide)))
        (sub_ne_zero.mpr (hinj.ne (by decide))))
      (sub_ne_zero.mpr (hinj.ne (by decide)))
  have h01 : ‖a 0-a 1‖ ≤ 2*‖a 1‖ := by
    have h := norm_sub_le (a 0) (a 1)
    linarith only [h,hAB]
  have h02 : ‖a 0-a 2‖ ≤ 2*‖a 2‖ := by
    have h := norm_sub_le (a 0) (a 2)
    linarith only [h,hAB,hBS]
  have h12 : ‖a 1-a 2‖ ≤ 2*‖a 2‖ := by
    have h := norm_sub_le (a 1) (a 2)
    linarith only [h,hBS]
  have hD : ‖coherentVandermonde3 a‖ ≤ 8*‖a 1‖*‖a 2‖^2 := by
    calc
      _ = ‖a 0-a 1‖*‖a 0-a 2‖*‖a 1-a 2‖ := by simp only [coherentVandermonde3,norm_mul]
      _ ≤ (2*‖a 1‖)*(2*‖a 2‖)*(2*‖a 2‖) :=
        mul_le_mul (mul_le_mul h01 h02 (norm_nonneg _) (by positivity)) h12
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨div_pos (norm_pos_iff.mpr hDelta) (by positivity), ?_⟩
  apply (div_le_iff₀ (by positivity : 0<‖a 1‖*‖a 2‖^2)).2
  nlinarith only [hD]



end D1Bound5
end
