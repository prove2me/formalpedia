-- Prove2me | solution 1 for DimdPolyLEAN.summable_realHermiteTensorL2_coeff_smul_of_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:16.73021+00:00
-- url     : https://prove2.me/submissions/681b932d-adc2-40e3-9de0-eac45c77a6e5

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
    {d : Nat} (kappa : MultiIndex d)
    (horth : Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha))
    (U : Skappa d kappa) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha • realHermiteTensorL2 alpha) := by
  classical
  have hOrthogonalFamily := horth.orthogonalFamily
  have hcoeff := U.summable_norm_sq
  exact
    (hOrthogonalFamily.summable_iff_norm_sq_summable
      (fun alpha : Idx d => coeffSkappa U alpha)).2 hcoeff
end DimdPolyLEAN
