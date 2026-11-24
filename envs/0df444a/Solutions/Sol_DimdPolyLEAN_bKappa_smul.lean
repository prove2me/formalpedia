-- Prove2me | solution 1 for DimdPolyLEAN.bKappa_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:51.239805+00:00
-- url     : https://prove2.me/submissions/c6fd17d4-254c-4739-8526-fdd30c8029de

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
    {d : Nat} (kappa : MultiIndex d) (w : ℂ) (U : Skappa d kappa) :
    bKappa kappa (w • U) = w • bKappa kappa U := by
  classical
  unfold bKappa
  calc
    (∑' alpha : Idx d, coeffSkappa (w • U) alpha • realHermiteTensorL2 alpha) =
        ∑' alpha : Idx d, w • (coeffSkappa U alpha • realHermiteTensorL2 alpha) := by
          apply tsum_congr
          intro alpha
          change (w * U.coeff alpha) • realHermiteTensorL2 alpha =
            w • (U.coeff alpha • realHermiteTensorL2 alpha)
          rw [smul_smul]
    _ = w • ∑' alpha : Idx d, coeffSkappa U alpha • realHermiteTensorL2 alpha := by
          rw [tsum_const_smul'']
end DimdPolyLEAN
