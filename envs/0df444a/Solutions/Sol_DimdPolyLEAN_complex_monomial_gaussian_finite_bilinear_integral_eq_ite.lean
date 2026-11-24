-- Prove2me | solution 1 for DimdPolyLEAN.complex_monomial_gaussian_finite_bilinear_integral_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:55.146242+00:00
-- url     : https://prove2.me/submissions/b2c1ca6c-2d5b-4e86-bf0a-929218aeebb8

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
public import Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_product_integral_eq_ite
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
    (∫ x : ℝ,
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (complexMonomialGaussian k x *
            complexMonomialGaussian l x)) =
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (if Even (k + l) then
            (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ)
          else 0) := by
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro l hl
      rw [MeasureTheory.integral_const_mul]
      rw [complex_monomial_gaussian_product_integral_eq_ite]
    · intro l hl
      exact (complex_monomial_gaussian_product_integrable k l).const_mul
        (a k * b l)
  · intro k hk
    exact monomial_gaussian_bilinear_row_integrable t a b k
end DimdPolyLEAN
