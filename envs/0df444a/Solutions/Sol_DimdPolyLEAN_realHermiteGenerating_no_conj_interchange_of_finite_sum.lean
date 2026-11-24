-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_no_conj_interchange_of_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:35.245329+00:00
-- url     : https://prove2.me/submissions/c4632f24-9197-4faf-a19f-9dde7bdc4272

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_inner_eq_factorial
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
    (n m : ℕ) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv m (realHermiteGenerating t) 0) =
      iteratedDeriv m
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0 := by
  have hleft := realHermiteGenerating_iteratedDeriv_inner_eq_factorial n m
  have hright :
      iteratedDeriv m
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0 =
        if n = m then (Nat.factorial n : ℂ) else 0 := by
    calc
      iteratedDeriv m
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0 =
          iteratedDeriv m
            (fun w : ℂ =>
              iteratedDeriv n (fun u : ℂ => Complex.exp (u * w)) 0) 0 := by
            congr 1
            funext w
            congr 1
            funext u
            rw [realHermiteGenerating_integral_mul]
      _ = if n = m then (Nat.factorial n : ℂ) else 0 := by
            simpa [eq_comm] using iteratedDeriv_iteratedDeriv_cexp_mul_at_zero m n
  exact hleft.trans hright.symm
end DimdPolyLEAN
