-- Prove2me | solution 1 for DimdPolyLEAN.bKappaRep_isL2Rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:19.803887+00:00
-- url     : https://prove2.me/submissions/3cad0ada-8b7d-4639-9e13-b492ef46e41d

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

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) :
    IsL2Rep (bKappa kappa U) (bKappaRep kappa U) := by
  refine ⟨MeasureTheory.Lp.memLp (bKappa kappa U), ?_⟩
  apply MeasureTheory.Lp.ext
  exact (MeasureTheory.Lp.memLp (bKappa kappa U)).coeFn_toLp
end DimdPolyLEAN
