-- Prove2me | solution 1 for D1Bound5.coherentRemainder_three_parameter_norm_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:37:43.204245+00:00
-- url     : https://prove2.me/submissions/a3e949e6-c92a-4440-9f10-cfffbd97576b

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
import Definitions.Def_D1Bound5_CoherentFormBounds_Definitions
import Definitions.Def_D1Bound5_CoherentThreeParameters_Definitions
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_coherentRemainder_norm_sub_le
import Theorems.Thm_D1Bound5_coherent_three_tail_factor_le
import Theorems.Thm_D1Bound5_halfBinomialCoeff_recurrence
import Theorems.Thm_D1Bound5_halfBinomialWeightedCoeff_three_norm_bounds

section
open Finset

noncomputable section

namespace D1Bound5







private theorem coherent_parameter_coeff_four : halfBinomialCoeff 4 = -5/128 := by
  have h1 : halfBinomialCoeff 1 = 1/2 := by
    norm_num [halfBinomialCoeff, Ring.choose_one_right]
  have h2 : halfBinomialCoeff 2 = -1/8 := by
    have h := halfBinomialCoeff_recurrence 1
    norm_num [h1] at h
    linarith
  have h3 : halfBinomialCoeff 3 = 1/16 := by
    have h := halfBinomialCoeff_recurrence 2
    norm_num [h2] at h
    linarith
  have h := halfBinomialCoeff_recurrence 3
  norm_num [h3] at h
  linarith





/-- Exact two-sided bounds for the actual complete homogeneous
three-anchor remainder in the manuscript parameter regime. -/
theorem _root_.solution
    (a : Fin 3 → ℂ) (p q : ℂ) (A P H : ℝ)
    (hA : 0 < A) (hP : 0 < P) (ha : ∀ i, A ≤ ‖a i‖)
    (hp : ‖p⁻¹‖ = 1/P) (hq : ‖q⁻¹‖ ≤ 1/(4*P))
    (hH : 1 < H) (hAP : H ≤ A*P) :
    coherentThreeLowerConstant H / P^3 ≤ ‖coherentRemainder a p q‖ ∧
    ‖coherentRemainder a p q‖ ≤ coherentThreeUpperConstant H / P^3 := by
  have hq' : ‖q⁻¹‖ ≤ 1/P :=
    hq.trans (one_div_le_one_div_of_le hP (by nlinarith))
  have ht := coherentRemainder_norm_sub_le a (by decide) p q A P hA hP ha hp.le hq'
    (hH.trans_le hAP)
  norm_num [coherent_parameter_coeff_four] at ht
  have hfactor := coherent_three_tail_factor_le A P H hH hAP
  have htail : ‖coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 3‖ ≤
      coherentThreeTailConstant H/P^3 := by
    calc
      _ ≤ (5/32 : ℝ)/P^3*(1/(1-1/(A*P))^3-1) := by
        simpa only [one_div, mul_inv_rev] using ht
      _ ≤ (5/32 : ℝ)/P^3*((H/(H-1))^3-1) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = _ := by dsimp [coherentThreeTailConstant]; ring
  obtain ⟨hcLow,hcUp⟩ := halfBinomialWeightedCoeff_three_norm_bounds p⁻¹ q⁻¹ P hP hp hq
  have hLowTriangle : ‖halfBinomialWeightedCoeff p⁻¹ q⁻¹ 3‖ ≤
      ‖coherentRemainder a p q‖ +
        ‖coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 3‖ := by
    have h := norm_sub_le (coherentRemainder a p q)
      (coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 3)
    simpa only [sub_sub_cancel] using h
  have hUpTriangle : ‖coherentRemainder a p q‖ ≤
      ‖halfBinomialWeightedCoeff p⁻¹ q⁻¹ 3‖ +
        ‖coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 3‖ := by
    have h := norm_add_le (halfBinomialWeightedCoeff p⁻¹ q⁻¹ 3)
      (coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 3)
    have heq : halfBinomialWeightedCoeff p⁻¹ q⁻¹ 3 +
        (coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 3) =
        coherentRemainder a p q := by ring
    rw [heq] at h
    exact h
  constructor
  · have heq : coherentThreeLowerConstant H/P^3 =
        45/(1024*P^3)-coherentThreeTailConstant H/P^3 := by
      dsimp [coherentThreeLowerConstant]
      field_simp
    rw [heq]
    linarith only [hLowTriangle,hcLow,htail]
  · have heq : coherentThreeUpperConstant H/P^3 =
        85/(1024*P^3)+coherentThreeTailConstant H/P^3 := by
      dsimp [coherentThreeUpperConstant]
      field_simp
    rw [heq]
    linarith only [hUpTriangle,hcUp,htail]



end D1Bound5
end
