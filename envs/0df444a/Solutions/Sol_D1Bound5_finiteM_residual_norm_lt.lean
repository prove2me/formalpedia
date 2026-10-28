-- Prove2me | solution 1 for D1Bound5.finiteM_residual_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:16.435409+00:00
-- url     : https://prove2.me/submissions/cb0f7a33-cdfe-446f-ac78-d12f9dc480b1

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions
import Definitions.Def_D1Bound5_FiniteMResidualPoint_Definitions
import Theorems.Thm_D1Bound5_finiteMRowFactor_ne_zero
import Theorems.Thm_D1Bound5_finiteM_residual_norm_lt_point
import Theorems.Thm_D1Bound5_finiteM_rowfactor_scalar

section
namespace D1Bound5



/-- The actual constructed M matrix has the manuscript's residual bound.
Its constant comes from |choose(5/2,8)|=45/32768 and the proved exact
arbitrary-order residue cancellation. -/
theorem _root_.solution (a b s c : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s)
    (hA1 : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hAC : 1000 ≤ ‖a‖*‖c‖) (i : Fin 4) :
    ‖finiteMResidual a b s c i‖ <
      (3920/81 : ℝ)*‖b‖^2*‖s‖^5/(‖a‖^3*‖c‖^6) := by
  have hA := norm_pos_iff.mpr ha
  have hB := norm_pos_iff.mpr hb
  have hS := norm_pos_iff.mpr hs
  have hC := norm_pos_iff.mpr hc
  have hx := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hy := norm_pos_iff.mpr (sub_ne_zero.mpr has)
  have hz := norm_pos_iff.mpr (sub_ne_zero.mpr hbs)
  have hrow := norm_pos_iff.mpr (finiteMRowFactor_ne_zero a b s ha hb hs hab has hbs i)
  have hr : ‖finiteMRowFactor a b s i‖ = ‖a-b‖*‖a-s‖*‖b-s‖ ∨
      ‖finiteMRowFactor a b s i‖ = ‖a‖*‖b-s‖ ∨
      ‖finiteMRowFactor a b s i‖ = ‖b‖*‖a-s‖ ∨
      ‖finiteMRowFactor a b s i‖ = ‖s‖*‖a-b‖ := by
    fin_cases i <;> simp [finiteMRowFactor, norm_mul]
  have hdiffAB : ‖a-b‖ ≤ 2*‖b‖ := (norm_sub_le a b).trans (by linarith)
  have hdiffAS : ‖a-s‖ ≤ 2*‖s‖ := (norm_sub_le a s).trans (by linarith)
  have hdiffBS : ‖b-s‖ ≤ 2*‖s‖ := (norm_sub_le b s).trans (by linarith)
  have hgeom := finiteM_rowfactor_scalar ‖a‖ ‖b‖ ‖s‖ ‖a-b‖ ‖a-s‖ ‖b-s‖
    ‖finiteMRowFactor a b s i‖ hA1 hAB hBS hx hy hz hdiffAB hdiffAS hdiffBS hr
  have hratio : ‖a‖*(‖a-b‖*‖a-s‖*‖b-s‖)^4 /
      (‖b‖^4*‖s‖^7*‖finiteMRowFactor a b s i‖) ≤ 2048 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hgeom])
  apply (finiteM_residual_norm_lt_point a b s c ha hb hs hc hab has hbs hAB hBS hAC i).trans_le
  have halg : (101/100 : ℝ)*(45/2048)*(‖a-b‖*‖a-s‖*‖b-s‖)^4 /
      (‖a‖^2*‖b‖^2*‖s‖^2*‖c‖^6*‖finiteMRowFactor a b s i‖) =
      (909/40960 : ℝ)*(‖a‖*(‖a-b‖*‖a-s‖*‖b-s‖)^4 /
        (‖b‖^4*‖s‖^7*‖finiteMRowFactor a b s i‖))*
          (‖b‖^2*‖s‖^5/(‖a‖^3*‖c‖^6)) := by
    field_simp [hA.ne', hB.ne', hS.ne', hC.ne', hrow.ne']
    <;> ring
  rw [halg]
  calc
    _ ≤ (909/40960 : ℝ)*2048*(‖b‖^2*‖s‖^5/(‖a‖^3*‖c‖^6)) := by gcongr
    _ ≤ (3920/81 : ℝ)*(‖b‖^2*‖s‖^5/(‖a‖^3*‖c‖^6)) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by ring

end D1Bound5
end
