-- Prove2me | solution 1 for DimdPolyLEAN.integral_real_mul_exp_neg_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:29.141673+00:00
-- url     : https://prove2.me/submissions/337e261d-bfb2-43f3-b1a0-d50975df500f

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
theorem _root_.solution :
    (∫ x : ℝ, x * Real.exp (-(x ^ (2 : ℕ)))) = 0 := by
  have h := MeasureTheory.integral_neg_eq_self
    (f := fun x : ℝ => x * Real.exp (-(x ^ (2 : ℕ))))
    (μ := (volume : MeasureTheory.Measure ℝ))
  rw [show (fun x : ℝ => (-x) * Real.exp (-((-x) ^ (2 : ℕ)))) =
      fun x : ℝ => -(x * Real.exp (-(x ^ (2 : ℕ)))) by
    simp_all only [even_two, Even.neg_pow, neg_mul]]
    at h
  rw [MeasureTheory.integral_neg] at h
  linarith only [h]
end DimdPolyLEAN
