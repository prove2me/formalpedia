-- Prove2me | solution 1 for DimdPolyLEAN.complex_monomial_gaussian_product_integral_of_eq_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:05.042087+00:00
-- url     : https://prove2.me/submissions/2bb7ccfc-e22f-4b94-867a-771cf6ef6a4a

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
open scoped Nat
namespace DimdPolyLEAN
theorem _root_.solution
    {k l r : ℕ} (hkl : k + l = 2 * r) :
    (∫ t : ℝ,
      complexMonomialGaussian k t * complexMonomialGaussian l t) =
      (((((2 * r - 1 : ℕ)‼ : ℕ) : ℝ) * Real.sqrt Real.pi /
        (2 ^ r : ℝ)) : ℂ) := by
  have heven : Even (k + l) := by
    simp_all only [even_two, Even.mul_right]
  rw [complex_monomial_gaussian_product_integral_of_even heven]
  rw [show ((((k + l : ℕ) : ℝ) + 1) / 2) = (r : ℝ) + 1 / 2 by
    rw [hkl]
    norm_num
    ring]
  rw [Real.Gamma_nat_add_half, Complex.ofReal_div, Complex.ofReal_mul]
end DimdPolyLEAN
