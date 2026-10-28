-- Prove2me | solution 1 for D1Bound5.coherentRemainder_four_parameter_norm_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:44:48.500892+00:00
-- url     : https://prove2.me/submissions/822449d8-b20a-43a1-81f7-1442b5a7dad4

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
import Definitions.Def_D1Bound5_CoherentFourParameters_Definitions
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_coherentRemainder_norm_sub_le
import Theorems.Thm_D1Bound5_halfBinomialCoeff_recurrence
import Theorems.Thm_D1Bound5_halfBinomialWeightedCoeff_four_norm_bounds

section
open Finset

noncomputable section

namespace D1Bound5











private theorem coherent_parameter_coeff_five : halfBinomialCoeff 5 = 7/256 := by
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
  have h4 : halfBinomialCoeff 4 = -5/128 := by
    have h := halfBinomialCoeff_recurrence 3
    norm_num [h3] at h
    linarith
  have h := halfBinomialCoeff_recurrence 4
  norm_num [h4] at h
  linarith



/-- Two-sided actual remainder bounds in the direct-four regime. -/
theorem _root_.solution
    (a : Fin 4 → ℂ) (p q : ℂ) (A P : ℝ)
    (hA : 0 < A) (hP : 0 < P) (ha : ∀ i, A ≤ ‖a i‖)
    (hp : ‖p⁻¹‖ = 1/P) (hq : ‖q⁻¹‖ ≤ 1/(1000*P))
    (hAP : 1000 ≤ A*P) :
    coherentFourLowerConstant/P^4 ≤ ‖coherentRemainder a p q‖ ∧
    ‖coherentRemainder a p q‖ ≤ coherentFourUpperConstant/P^4 := by
  have hq' : ‖q⁻¹‖ ≤ 1/P := hq.trans
    (one_div_le_one_div_of_le hP (by nlinarith))
  have ht := coherentRemainder_norm_sub_le a (by decide) p q A P hA hP ha hp.le hq' (by linarith)
  norm_num [coherent_parameter_coeff_five] at ht
  have hinv : 1/(A*P) ≤ (1/1000 : ℝ) := one_div_le_one_div_of_le (by norm_num) hAP
  have hbase : (999/1000 : ℝ) ≤ 1-1/(A*P) := by linarith
  have hbase4 : (999/1000 : ℝ)^4 ≤ (1-1/(A*P))^4 := by gcongr
  have hfactor : 1/(1-1/(A*P))^4-1 ≤ (1000/999 : ℝ)^4-1 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<(999/1000:ℝ)^4) hbase4
    norm_num at h ⊢
    linarith
  have htail : ‖coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 4‖ ≤
      coherentFourTailConstant/P^4 := by
    calc
      _ ≤ (7/64 : ℝ)/P^4*(1/(1-1/(A*P))^4-1) := by
        simpa only [one_div, mul_inv_rev] using ht
      _ ≤ (7/64 : ℝ)/P^4*((1000/999 : ℝ)^4-1) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = _ := by dsimp [coherentFourTailConstant]; ring
  obtain ⟨hcLow,hcUp⟩ := halfBinomialWeightedCoeff_four_norm_bounds p⁻¹ q⁻¹ P hP hp hq
  have hLowTriangle : ‖halfBinomialWeightedCoeff p⁻¹ q⁻¹ 4‖ ≤
      ‖coherentRemainder a p q‖ +
        ‖coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 4‖ := by
    have h := norm_sub_le (coherentRemainder a p q)
      (coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 4)
    simpa only [sub_sub_cancel] using h
  have hUpTriangle : ‖coherentRemainder a p q‖ ≤
      ‖halfBinomialWeightedCoeff p⁻¹ q⁻¹ 4‖ +
        ‖coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 4‖ := by
    have h := norm_add_le (halfBinomialWeightedCoeff p⁻¹ q⁻¹ 4)
      (coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 4)
    have heq : halfBinomialWeightedCoeff p⁻¹ q⁻¹ 4 +
        (coherentRemainder a p q-halfBinomialWeightedCoeff p⁻¹ q⁻¹ 4) =
        coherentRemainder a p q := by ring
    rw [heq] at h
    exact h
  constructor
  · have heq : coherentFourLowerConstant/P^4 =
        coherentFourLeadingLower/P^4-coherentFourTailConstant/P^4 := by
      dsimp [coherentFourLowerConstant]
      ring
    rw [heq]
    linarith only [hLowTriangle,hcLow,htail]
  · have heq : coherentFourUpperConstant/P^4 =
        coherentFourLeadingUpper/P^4+coherentFourTailConstant/P^4 := by
      dsimp [coherentFourUpperConstant]
      ring
    rw [heq]
    linarith only [hUpTriangle,hcUp,htail]



end D1Bound5
end
