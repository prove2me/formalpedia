-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteTensorL2_inner_eq_integral_of_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:16.682688+00:00
-- url     : https://prove2.me/submissions/9a9752e7-1dab-443c-b996-b0f199f55ca1

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteTensorL2_eq_toLp_of_memLp
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
    {d : Nat} (alpha beta : Idx d)
    (hα : MemLp (realHermiteTensorRep alpha) 2
      (volume : Measure (RealVec d)))
    (hβ : MemLp (realHermiteTensorRep beta) 2
      (volume : Measure (RealVec d))) :
    inner ℂ (realHermiteTensorL2 alpha) (realHermiteTensorL2 beta) =
      ∫ x : RealVec d,
        realHermiteTensorRep beta x * star (realHermiteTensorRep alpha x) := by
  rw [realHermiteTensorL2_eq_toLp_of_memLp alpha hα,
    realHermiteTensorL2_eq_toLp_of_memLp beta hβ, MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hα.coeFn_toLp, hβ.coeFn_toLp] with x hαx hβx
  simp_all only [RCLike.inner_apply, RCLike.star_def]
end DimdPolyLEAN
