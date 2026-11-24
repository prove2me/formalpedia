-- Prove2me | solution 1 for DimdPolyLEAN.iteratedDeriv_iteratedDeriv_cexp_mul_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:14.887308+00:00
-- url     : https://prove2.me/submissions/3ac57835-b850-4c4d-b918-923062bed793

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
public import Theorems.Thm_DimdPolyLEAN_iteratedDeriv_cexp_mul_right_at_zero
public import Theorems.Thm_DimdPolyLEAN_iteratedDeriv_pow_at_zero

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution (m n : ℕ) :
    iteratedDeriv m
      (fun w : ℂ => iteratedDeriv n (fun u : ℂ => Complex.exp (u * w)) 0) 0 =
      if m = n then (Nat.factorial n : ℂ) else 0 := by
  have hfun :
      (fun w : ℂ => iteratedDeriv n (fun u : ℂ => Complex.exp (u * w)) 0) =
        fun w : ℂ => w ^ n := by
    funext w
    exact iteratedDeriv_cexp_mul_right_at_zero n w
  rw [hfun]
  exact iteratedDeriv_pow_at_zero m n
end DimdPolyLEAN
