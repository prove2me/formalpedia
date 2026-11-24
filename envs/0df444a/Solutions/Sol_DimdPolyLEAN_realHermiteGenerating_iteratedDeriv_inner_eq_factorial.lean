-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_iteratedDeriv_inner_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:33.91929+00:00
-- url     : https://prove2.me/submissions/2c4aa21b-f9b7-4586-86ba-b8e037b33b5e

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_inner_finite_sum
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_inner_finite_sum_eq_factorial

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
      if n = m then (Nat.factorial n : ℂ) else 0 := by
  rw [realHermiteGenerating_iteratedDeriv_inner_finite_sum]
  exact realHermiteGenerating_inner_finite_sum_eq_factorial n m
end DimdPolyLEAN
