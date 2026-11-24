-- Prove2me | solution 1 for DimdPolyLEAN.complex_monomial_gaussian_finite_bilinear_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:15.52229+00:00
-- url     : https://prove2.me/submissions/1ed8fd1c-bf30-45c6-b699-ff05653fbae2

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
public import Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_product_integrable
section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
private theorem monomial_gaussian_bilinear_row_integrable
    (t : Finset ℕ) (a b : ℕ → ℂ) (k : ℕ) :
    Integrable
      (fun x : ℝ =>
        ∑ l ∈ t,
          (a k * b l) *
            (complexMonomialGaussian k x * complexMonomialGaussian l x))
      (volume : Measure ℝ) := by
  refine MeasureTheory.integrable_finsetSum t ?_
  intro l hl
  exact (complex_monomial_gaussian_product_integrable k l).const_mul (a k * b l)
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    (s t : Finset ℕ) (a b : ℕ → ℂ) :
    Integrable
      (fun x : ℝ =>
        ∑ k ∈ s, ∑ l ∈ t,
          (a k * b l) *
            (complexMonomialGaussian k x *
              complexMonomialGaussian l x))
      (volume : Measure ℝ) := by
  refine MeasureTheory.integrable_finsetSum s ?_
  intro k hk
  exact monomial_gaussian_bilinear_row_integrable t a b k
end DimdPolyLEAN
