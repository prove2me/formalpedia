-- Prove2me | solution 1 for D1Bound5.bennettTwoRowForm_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:44:14.859932+00:00
-- url     : https://prove2.me/submissions/8210ca24-4745-4ca4-ad94-a780072892be

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
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
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettIntegralRowSelection_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_bennettTwoClearedEntry_residual_norm_lt_half_rate
import Theorems.Thm_D1Bound5_bennettTwoClearedEntry_weighted_height
import Theorems.Thm_D1Bound5_bennettTwoRowForm_norm_le

section
open scoped NumberField
open Module

namespace D1Bound5



/-- The actual determinant row, coefficient bounds, and residual bound
give the manuscript's all-order upper estimate once the two root errors
have been produced. The following full-ring theorem produces them. -/
theorem _root_.solution
    (a b c z sA sB : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hab : a ≠ b) (hz : z ≠ 0)
    (hAB : ‖a‖ ≤ ‖b‖) (hAC : 1000 ≤ ‖a‖ * ‖c‖)
    (herrorA : ‖(1 + 1 / (a * c)) ^ (1 / 2 : ℂ) - sA / (a * z)‖ <
      (3 / 2 : ℝ) * ‖c‖ / (‖a‖ * ‖z‖ ^ 2))
    (herrorB : ‖(1 + 1 / (b * c)) ^ (1 / 2 : ℂ) - sB / (b * z)‖ <
      (3 / 2 : ℝ) * ‖c‖ / (‖b‖ * ‖z‖ ^ 2))
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ‖bennettTwoRowForm a b c z sA sB k i‖ <
      3 * ‖c‖ * (42 * ‖b‖ ^ 3 * ‖c‖) ^ k / (‖b‖ * ‖z‖) +
        ‖z‖ / (2 * (bennettTwoResidualRate ‖a‖ ‖b‖ ‖c‖ ‖a - b‖) ^ k) := by
  let Q : Fin 3 → ℂ := fun j => bennettTwoClearedEntry a b c k i j
  let θA : ℂ := (1 + 1 / (a * c)) ^ (1 / 2 : ℂ)
  let θB : ℂ := (1 + 1 / (b * c)) ^ (1 / 2 : ℂ)
  let R : ℂ := ∑ j, Q j *
    (1 + bennettTwoNodes a b j * (a * b * c)⁻¹) ^ (1 / 2 : ℂ)
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hB : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hC : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hZ : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hres := bennettTwoClearedEntry_residual_norm_lt_half_rate
    a b c ha hb hc hab hAB (by linarith) k hk i
  have hres' : ‖z‖ * ‖R‖ <
      ‖z‖ / (2 * (bennettTwoResidualRate ‖a‖ ‖b‖ ‖c‖ ‖a - b‖) ^ k) := by
    calc
      _ < ‖z‖ * (1 / (2 * (bennettTwoResidualRate ‖a‖ ‖b‖ ‖c‖ ‖a - b‖) ^ k)) :=
        mul_lt_mul_of_pos_left hres hZ
      _ = _ := by ring
  have herrors : ‖z‖ * (‖Q 1‖ * ‖θA - sA / (a * z)‖ +
        ‖Q 2‖ * ‖θB - sB / (b * z)‖) ≤
      ‖z‖ * (‖Q 1‖ * ((3 / 2 : ℝ) * ‖c‖ / (‖a‖ * ‖z‖ ^ 2)) +
        ‖Q 2‖ * ((3 / 2 : ℝ) * ‖c‖ / (‖b‖ * ‖z‖ ^ 2))) := by
    apply mul_le_mul_of_nonneg_left _ hZ.le
    exact add_le_add
      (mul_le_mul_of_nonneg_left herrorA.le (norm_nonneg _))
      (mul_le_mul_of_nonneg_left herrorB.le (norm_nonneg _))
  have hscale : ‖z‖ * (‖Q 1‖ * ((3 / 2 : ℝ) * ‖c‖ / (‖a‖ * ‖z‖ ^ 2)) +
        ‖Q 2‖ * ((3 / 2 : ℝ) * ‖c‖ / (‖b‖ * ‖z‖ ^ 2))) =
      ((3 / 2 : ℝ) * ‖c‖ / ‖z‖) * (‖Q 1‖ / ‖a‖ + ‖Q 2‖ / ‖b‖) := by
    field_simp [hA.ne', hB.ne', hZ.ne']
    <;> ring
  have hheight := bennettTwoClearedEntry_weighted_height
    a b c ha hb hc hab hAB hAC k hk i
  have herror' : ‖z‖ * (‖Q 1‖ * ‖θA - sA / (a * z)‖ +
        ‖Q 2‖ * ‖θB - sB / (b * z)‖) <
      3 * ‖c‖ * (42 * ‖b‖ ^ 3 * ‖c‖) ^ k / (‖b‖ * ‖z‖) := by
    calc
      _ ≤ _ := herrors
      _ = ((3 / 2 : ℝ) * ‖c‖ / ‖z‖) * (‖Q 1‖ / ‖a‖ + ‖Q 2‖ / ‖b‖) := hscale
      _ < ((3 / 2 : ℝ) * ‖c‖ / ‖z‖) *
          (2 * (42 * ‖b‖ ^ 3 * ‖c‖) ^ k / ‖b‖) :=
        mul_lt_mul_of_pos_left hheight (by positivity)
      _ = _ := by field_simp [hB.ne', hZ.ne']
  calc
    _ ≤ ‖z‖ * ‖R‖ + ‖z‖ * (‖Q 1‖ * ‖θA - sA / (a * z)‖ +
        ‖Q 2‖ * ‖θB - sB / (b * z)‖) :=
      bennettTwoRowForm_norm_le a b c z sA sB ha hb hc hz k i
    _ < ‖z‖ / (2 * (bennettTwoResidualRate ‖a‖ ‖b‖ ‖c‖ ‖a - b‖) ^ k) +
        3 * ‖c‖ * (42 * ‖b‖ ^ 3 * ‖c‖) ^ k / (‖b‖ * ‖z‖) :=
      add_lt_add hres' herror'
    _ = _ := add_comm _ _



end D1Bound5
end
