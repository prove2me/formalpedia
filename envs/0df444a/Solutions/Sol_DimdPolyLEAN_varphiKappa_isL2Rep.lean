-- Prove2me | solution 1 for DimdPolyLEAN.varphiKappa_isL2Rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:32.262945+00:00
-- url     : https://prove2.me/submissions/cf0e8f04-0bdc-426d-b9cf-1472839f6092

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
public import Theorems.Thm_DimdPolyLEAN_realHermite1D_memLp_inner_orthonormal
public import Theorems.Thm_DimdPolyLEAN_realHermiteTensorRep_memLp_of_realHermite1D_memLp
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



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
    IsL2Rep (varphiKappa kappa) (realHermiteTensorRep kappa) := by
  have hmem :
      MemLp (realHermiteTensorRep kappa) 2
        (volume : Measure (RealVec d)) :=
    realHermiteTensorRep_memLp_of_realHermite1D_memLp kappa
      realHermite1D_memLp_inner_orthonormal.1
  refine ⟨hmem, ?_⟩
  unfold varphiKappa
  simp [hmem]
end DimdPolyLEAN
