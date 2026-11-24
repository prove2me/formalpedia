-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_iteratedDeriv_inner_of_no_conj_interchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:39.070283+00:00
-- url     : https://prove2.me/submissions/7baeb331-82f0-4db6-bee2-279dd52d8b03

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_integral_mul
public import Theorems.Thm_DimdPolyLEAN_iteratedDeriv_iteratedDeriv_cexp_mul_at_zero
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_zero_star
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
    (n m : ℕ)
    (hinterchange :
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating t) 0 *
          iteratedDeriv m (realHermiteGenerating t) 0) =
        iteratedDeriv m
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        star (iteratedDeriv m (realHermiteGenerating t) 0)) =
      if n = m then (Nat.factorial n : ℂ) else 0 := by
  calc
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        star (iteratedDeriv m (realHermiteGenerating t) 0)) =
        ∫ t : ℝ,
          iteratedDeriv n (realHermiteGenerating t) 0 *
            iteratedDeriv m (realHermiteGenerating t) 0 := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          rw [realHermiteGenerating_iteratedDeriv_zero_star]
    _ = iteratedDeriv m
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0 := hinterchange
    _ = iteratedDeriv m
          (fun w : ℂ => iteratedDeriv n (fun u : ℂ => Complex.exp (u * w)) 0) 0 := by
          congr 1
          funext w
          congr 1
          funext u
          rw [realHermiteGenerating_integral_mul]
    _ = if n = m then (Nat.factorial n : ℂ) else 0 := by
          simpa [eq_comm] using iteratedDeriv_iteratedDeriv_cexp_mul_at_zero m n
end DimdPolyLEAN
