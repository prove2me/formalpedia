-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_deriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:34.92643+00:00
-- url     : https://prove2.me/submissions/8970b232-9323-427b-97bb-577d0d654e31

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
theorem _root_.solution (t : ℝ) :
    deriv (realHermiteGenerating t) 0 =
      (Real.sqrt 2 : ℂ) * (t : ℂ) * ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(((t : ℂ) ^ 2) / 2)) := by
  unfold realHermiteGenerating
  rw [deriv_const_mul]
  · rw [deriv_cexp]
    · rw [show deriv
          (fun u : ℂ => -(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * u -
            u ^ 2 / 2) 0 = (Real.sqrt 2 : ℂ) * (t : ℂ) by
        rw [show (fun u : ℂ => -(((t : ℂ) ^ 2) / 2) +
              (Real.sqrt 2 : ℂ) * (t : ℂ) * u - u ^ 2 / 2) =
            (fun u : ℂ => (Real.sqrt 2 : ℂ) * (t : ℂ) * u +
              (-(((t : ℂ) ^ 2) / 2) + u ^ 2 * (-1 / 2))) by
          funext u
          ring]
        rw [deriv_fun_add]
        · simp_all only [deriv_const_mul_id', differentiableAt_const, deriv_const_add',
            differentiableAt_fun_id, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_fun_pow,
            Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_zero, deriv_id'', mul_one, zero_mul,
            ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, deriv_div_const, deriv_const',
            zero_div, add_zero]
        · fun_prop
        · fun_prop]
      ring_nf
    · fun_prop
  · fun_prop
end DimdPolyLEAN
