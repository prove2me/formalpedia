-- Prove2me | solution 1 for DimdPolyLEAN.complex_monomial_gaussian_finite_bilinear_integral_eq_even_moments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:26.909647+00:00
-- url     : https://prove2.me/submissions/fa83abcf-b290-4764-a6d7-646de882d5c2

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
public import Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_finite_bilinear_integral_eq_ite
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
    (s t : Finset ℕ) (a b : ℕ → ℂ)
    (heven : ∀ k ∈ s, ∀ l ∈ t, Even (k + l)) :
    (∫ x : ℝ,
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (complexMonomialGaussian k x *
            complexMonomialGaussian l x)) =
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ) := by
  rw [complex_monomial_gaussian_finite_bilinear_integral_eq_ite]
  simp_all only [↓reduceIte, Nat.cast_add]
end DimdPolyLEAN
