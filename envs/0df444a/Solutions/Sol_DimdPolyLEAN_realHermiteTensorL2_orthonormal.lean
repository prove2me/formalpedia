-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteTensorL2_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:31.832946+00:00
-- url     : https://prove2.me/submissions/a4000017-6eff-4d27-8d33-d81e454da107

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteTensorL2_orthonormal_of_memLp_integral
public import Theorems.Thm_DimdPolyLEAN_realHermite1D_memLp_inner_orthonormal
public import Theorems.Thm_DimdPolyLEAN_realHermiteTensorRep_memLp_of_realHermite1D_memLp
public import Theorems.Thm_DimdPolyLEAN_realHermiteTensorRep_inner_of_realHermite1D_inner

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution {d : Nat} :
    Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha) := by
  /-
  This is the real-side analogue of `TensorBasis.PhiL2_orthonormal_family`.
  The remaining work is the real Hermite orthonormality package:
  one-dimensional real Hermite orthonormality in Lebesgue `L²(ℝ)`, tensorized
  over `RealVec d`, with `varphiKappa` unfolded through its `MemLp` branch.
  -/
  have hpackage :
      (∀ alpha : Idx d,
        MemLp (realHermiteTensorRep alpha) 2
          (volume : Measure (RealVec d))) ∧
        ∀ alpha beta : Idx d,
          (∫ x : RealVec d,
            realHermiteTensorRep beta x * star (realHermiteTensorRep alpha x)) =
            if alpha = beta then (1 : ℂ) else 0 := by
    exact
      ⟨fun alpha =>
          realHermiteTensorRep_memLp_of_realHermite1D_memLp alpha
            realHermite1D_memLp_inner_orthonormal.1,
        fun alpha beta =>
          realHermiteTensorRep_inner_of_realHermite1D_inner alpha beta
            realHermite1D_memLp_inner_orthonormal.2⟩
  exact realHermiteTensorL2_orthonormal_of_memLp_integral hpackage.1 hpackage.2
end DimdPolyLEAN
