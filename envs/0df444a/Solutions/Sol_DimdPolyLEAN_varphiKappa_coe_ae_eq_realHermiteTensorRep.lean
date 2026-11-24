-- Prove2me | solution 1 for DimdPolyLEAN.varphiKappa_coe_ae_eq_realHermiteTensorRep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:29.872962+00:00
-- url     : https://prove2.me/submissions/04b17288-9a3c-4dd1-a9cb-9ddd76cd21c7

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
public import Theorems.Thm_DimdPolyLEAN_varphiKappa_isL2Rep

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (kappa : MultiIndex d) :
    ((varphiKappa kappa : L2Real d) : RealVec d -> ℂ)
      =ᵐ[(volume : Measure (RealVec d))] realHermiteTensorRep kappa := by
  rcases varphiKappa_isL2Rep kappa with ⟨hmem, h_eq⟩
  rw [← h_eq]
  exact hmem.coeFn_toLp
end DimdPolyLEAN
