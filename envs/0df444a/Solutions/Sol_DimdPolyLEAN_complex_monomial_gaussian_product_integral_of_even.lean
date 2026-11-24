-- Prove2me | solution 1 for DimdPolyLEAN.complex_monomial_gaussian_product_integral_of_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:09.648515+00:00
-- url     : https://prove2.me/submissions/90f829a0-6cb7-4e58-afcb-5a961fa02b77

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
public import Theorems.Thm_DimdPolyLEAN_integral_real_pow_exp_neg_sq_of_even
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
    {k l : ℕ} (heven : Even (k + l)) :
    (∫ t : ℝ,
      complexMonomialGaussian k t * complexMonomialGaussian l t) =
      (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ) := by
  rw [show (fun t : ℝ =>
      complexMonomialGaussian k t * complexMonomialGaussian l t) =
      fun t : ℝ =>
        ((t ^ (k + l) * Real.exp (-(t ^ (2 : ℕ))) : ℝ) : ℂ) by
    funext t
    unfold complexMonomialGaussian
    let z : ℂ := (t : ℂ)
    let e : ℂ := Complex.exp (-(z ^ (2 : ℕ) / 2))
    change (z ^ k * e) * (z ^ l * e) =
      ((t ^ (k + l) * Real.exp (-(t ^ (2 : ℕ))) : ℝ) : ℂ)
    calc
      (z ^ k * e) * (z ^ l * e) =
          z ^ (k + l) * (e * e) := by
            rw [show (z ^ k * e) * (z ^ l * e) =
              (z ^ k * z ^ l) * (e * e) by ring]
            rw [← pow_add]
      _ = z ^ (k + l) * Complex.exp (-(z ^ (2 : ℕ))) := by
            rw [show e * e = Complex.exp (-(z ^ (2 : ℕ))) by
              simp only [e]
              rw [← Complex.exp_add]
              congr 1
              ring]
      _ = ((t ^ (k + l) * Real.exp (-(t ^ (2 : ℕ))) : ℝ) : ℂ) := by
            rw [show z ^ (k + l) = ((t ^ (k + l) : ℝ) : ℂ) by simp [z, ← Complex.ofReal_pow]]
            rw [show Complex.exp (-(z ^ (2 : ℕ))) =
                ((Real.exp (-(t ^ (2 : ℕ))) : ℝ) : ℂ) by
              rw [show -(z ^ (2 : ℕ)) = ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) by
                simp [z, ← Complex.ofReal_pow]]
              rw [← Complex.ofReal_exp]]
            rw [← Complex.ofReal_mul]]
  rw [integral_complex_ofReal, integral_real_pow_exp_neg_sq_of_even heven]
end DimdPolyLEAN
