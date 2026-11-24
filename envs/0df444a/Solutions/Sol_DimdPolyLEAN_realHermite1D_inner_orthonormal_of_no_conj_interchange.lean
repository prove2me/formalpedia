-- Prove2me | solution 1 for DimdPolyLEAN.realHermite1D_inner_orthonormal_of_no_conj_interchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:36.77137+00:00
-- url     : https://prove2.me/submissions/917e7b00-479b-4ba1-8766-bfa3a1a7343d

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
public import Theorems.Thm_DimdPolyLEAN_realHermite1D_inner_of_iteratedDeriv_inner
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_inner_of_no_conj_interchange
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
    (hinterchange : ∀ n m : ℕ,
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating t) 0 *
          iteratedDeriv m (realHermiteGenerating t) 0) =
        iteratedDeriv m
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0) :
    ∀ n m : Nat,
      (∫ t : ℝ, realHermite1D m t * star (realHermite1D n t)) =
        if n = m then (1 : ℂ) else 0 := by
  intro n m
  have hderiv :=
    realHermiteGenerating_iteratedDeriv_inner_of_no_conj_interchange
      m n (hinterchange m n)
  simpa [eq_comm] using realHermite1D_inner_of_iteratedDeriv_inner m n hderiv
end DimdPolyLEAN
