-- Prove2me | solution 1 for DimdPolyLEAN.bKappa_coeff_recovery_of_realHermite_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:53.483706+00:00
-- url     : https://prove2.me/submissions/72a6e15a-b1df-47a0-afb9-8ffc8adc536d

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
public import Theorems.Thm_DimdPolyLEAN_summable_realHermiteTensorL2_coeff_smul_of_orthonormal
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
    {d : Nat} (kappa : MultiIndex d)
    (horth : Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha))
    (U : Skappa d kappa) (beta : Idx d) :
    coeffSkappa U beta =
      inner ℂ (realHermiteTensorL2 beta) (bKappa kappa U) := by
  classical
  have hsummable :=
    summable_realHermiteTensorL2_coeff_smul_of_orthonormal kappa horth U
  unfold bKappa
  change coeffSkappa U beta =
    (innerSL ℂ (realHermiteTensorL2 beta))
      (∑' alpha : Idx d, coeffSkappa U alpha • realHermiteTensorL2 alpha)
  rw [ContinuousLinearMap.map_tsum
    (innerSL ℂ (realHermiteTensorL2 beta)) hsummable]
  rw [tsum_eq_single beta]
  · have hbb :
        inner ℂ (realHermiteTensorL2 beta) (realHermiteTensorL2 beta) = 1 := by
      simpa using orthonormal_iff_ite.mp horth beta beta
    change coeffSkappa U beta =
      inner ℂ (realHermiteTensorL2 beta)
        (coeffSkappa U beta • realHermiteTensorL2 beta)
    rw [inner_smul_right, hbb, mul_one]
  · intro alpha halpha
    have hba :
        inner ℂ (realHermiteTensorL2 beta) (realHermiteTensorL2 alpha) = 0 := by
      simpa [Ne.symm halpha] using orthonormal_iff_ite.mp horth beta alpha
    simp_all only [ne_eq, map_smul, coe_innerSL_apply, smul_eq_mul, mul_zero]
end DimdPolyLEAN
