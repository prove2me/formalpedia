-- Prove2me | solution 1 for DimdPolyLEAN.complex_monomial_gaussian_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:28.290896+00:00
-- url     : https://prove2.me/submissions/67f38c24-80bc-4f18-af68-75343d428272

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
public import Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_memLp

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
    Integrable
      (fun t : ℝ =>
        complexMonomialGaussian k t * complexMonomialGaussian l t)
      (volume : Measure ℝ) := by
  have hk : MemLp (complexMonomialGaussian k) 2 (volume : Measure ℝ) :=
    complex_monomial_gaussian_memLp k
  have hl : MemLp (complexMonomialGaussian l) 2 (volume : Measure ℝ) :=
    complex_monomial_gaussian_memLp l
  have hmul := hk.integrable_mul hl
  refine hmul.congr ?_
  filter_upwards with t
  rfl
end DimdPolyLEAN
