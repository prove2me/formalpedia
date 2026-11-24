-- Prove2me | solution 1 for DimdPolyLEAN.complex_monomial_gaussian_product_integral_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:08.252203+00:00
-- url     : https://prove2.me/submissions/929fadc3-6f25-4833-b557-563e4a1ca51c

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
theorem _root_.solution
    {k l : ℕ} (hodd : Odd (k + l)) :
    (∫ t : ℝ,
      complexMonomialGaussian k t * complexMonomialGaussian l t) = 0 := by
  let f : ℝ → ℂ :=
    fun t => complexMonomialGaussian k t * complexMonomialGaussian l t
  have hneg := MeasureTheory.integral_neg_eq_self
    (f := f) (μ := (volume : Measure ℝ))
  have hpoint : (fun t : ℝ => f (-t)) = fun t : ℝ => -f t := by
    funext t
    let z : ℂ := (t : ℂ)
    let e : ℂ := Complex.exp (-(z ^ (2 : ℕ) / 2))
    have hcast : ((-t : ℝ) : ℂ) = -z := by simp [z]
    simp only [f, complexMonomialGaussian, hcast]
    rw [show -((-z) ^ (2 : ℕ) / 2) = -(z ^ (2 : ℕ) / 2) by ring]
    change ((-z) ^ k * e) * ((-z) ^ l * e) =
      -((z ^ k * e) * (z ^ l * e))
    calc
      ((-z) ^ k * e) * ((-z) ^ l * e) =
          (-z) ^ (k + l) * (e * e) := by
            rw [show ((-z) ^ k * e) * ((-z) ^ l * e) =
              ((-z) ^ k * (-z) ^ l) * (e * e) by ring]
            rw [← pow_add]
      _ = -(z ^ (k + l) * (e * e)) := by
            rw [hodd.neg_pow]
            ring
      _ = -((z ^ k * e) * (z ^ l * e)) := by
            rw [show ((z ^ k * e) * (z ^ l * e)) =
              (z ^ k * z ^ l) * (e * e) by ring]
            rw [← pow_add]
  rw [hpoint, MeasureTheory.integral_neg] at hneg
  exact CharZero.neg_eq_self_iff.mp hneg
end DimdPolyLEAN
