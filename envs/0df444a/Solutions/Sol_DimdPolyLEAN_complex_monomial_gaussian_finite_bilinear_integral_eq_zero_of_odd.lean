-- Prove2me | solution 1 for DimdPolyLEAN.complex_monomial_gaussian_finite_bilinear_integral_eq_zero_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:26.489654+00:00
-- url     : https://prove2.me/submissions/e2ef685c-61b9-4128-9822-30940df61670

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
    (hodd : ∀ k ∈ s, ∀ l ∈ t, Odd (k + l)) :
    (∫ x : ℝ,
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (complexMonomialGaussian k x *
            complexMonomialGaussian l x)) = 0 := by
  rw [complex_monomial_gaussian_finite_bilinear_integral_eq_ite]
  refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl => ?_
  rw [if_neg (Nat.not_even_iff_odd.mpr (hodd k hk l hl)), mul_zero]
end DimdPolyLEAN
