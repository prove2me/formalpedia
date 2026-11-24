-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_iteratedDeriv_zero_product_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:05.612094+00:00
-- url     : https://prove2.me/submissions/fd4ec747-7004-4694-b820-676daa123fea

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_zero_expansion_monomial

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    (n m : ℕ) (t : ℝ) :
    iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv m (realHermiteGenerating t) 0 =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (complexMonomialGaussian k t *
            complexMonomialGaussian l t) := by
  rw [realHermiteGenerating_iteratedDeriv_zero_expansion_monomial n t,
    realHermiteGenerating_iteratedDeriv_zero_expansion_monomial m t]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring
end DimdPolyLEAN
