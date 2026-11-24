-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_iteratedDeriv_inner_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:04.016576+00:00
-- url     : https://prove2.me/submissions/5941d125-3b94-4b8f-b324-9c4dbbd998ef

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_zero_product_expansion

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    (n m : ℕ) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv m (realHermiteGenerating t) 0) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (if Even (k + l) then
            (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ)
          else 0) := by
  calc
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv m (realHermiteGenerating t) 0) =
        ∫ t : ℝ,
          ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
            (realHermiteGeneratingExpansionCoeff n k *
                realHermiteGeneratingExpansionCoeff m l) *
              (complexMonomialGaussian k t *
                complexMonomialGaussian l t) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          rw [realHermiteGenerating_iteratedDeriv_zero_product_expansion]
    _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (if Even (k + l) then
            (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ)
          else 0) := by
          exact complex_monomial_gaussian_finite_bilinear_integral_eq_ite
            (Finset.range (n + 1)) (Finset.range (m + 1))
            (realHermiteGeneratingExpansionCoeff n)
            (realHermiteGeneratingExpansionCoeff m)
end DimdPolyLEAN
