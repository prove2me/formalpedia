-- Prove2me | solution 1 for DimdPolyLEAN.complex_monomial_gaussian_product_integral_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:09.576208+00:00
-- url     : https://prove2.me/submissions/b71ca216-2168-40eb-8d93-5aed146d5bb0

module
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
public import Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_product_integral_of_odd
public import Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_product_integral_of_even
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    (k l : ℕ) :
    (∫ t : ℝ,
      complexMonomialGaussian k t * complexMonomialGaussian l t) =
      if Even (k + l) then
        (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ)
      else 0 := by
  by_cases heven : Even (k + l)
  · simp [heven, complex_monomial_gaussian_product_integral_of_even heven]
  · have hodd : Odd (k + l) := Nat.not_even_iff_odd.mp heven
    simp [heven, complex_monomial_gaussian_product_integral_of_odd hodd]
end DimdPolyLEAN
