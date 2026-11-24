-- Prove2me | solution 1 for DimdPolyLEAN.bKappa_injective_of_realHermite_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:49.961805+00:00
-- url     : https://prove2.me/submissions/43899ff7-3b77-4bf5-b05e-e4f3a25c8f76

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
public import Theorems.Thm_DimdPolyLEAN_bKappa_coeff_recovery_of_realHermite_orthonormal
public import Theorems.Thm_DimdPolyLEAN_bKappa_injective_of_realHermite_coeff_recovery

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (kappa : MultiIndex d)
    (horth : Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha)) :
    Function.Injective (bKappa kappa) :=
  bKappa_injective_of_realHermite_coeff_recovery kappa
    (fun U alpha =>
      bKappa_coeff_recovery_of_realHermite_orthonormal kappa horth U alpha)
end DimdPolyLEAN
