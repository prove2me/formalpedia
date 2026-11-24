-- Prove2me | solution 1 for DimdPolyLEAN.hasDerivAt_integral_shifted_generating_mul_modulated_right_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:16.401824+00:00
-- url     : https://prove2.me/submissions/692b995c-16db-4076-8b5c-219affd895ce

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_ambiguity_integral_independent_kernel
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
    (u w0 : ℂ) (x ω : ℝ) :
    HasDerivAt
      (fun w : ℂ => ∫ t : ℝ,
        realHermiteGenerating (t + x / 2) u *
          realHermiteGenerating (t - x / 2) w *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (ω * t : ℂ)))
      (((u -
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
          Complex.exp
            (u * w0 +
              (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * u -
                star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * w0)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))))
      w0 := by
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  change HasDerivAt _
    (((u - star z) * Complex.exp (u * w0 + z * u - star z * w0)) * E) w0
  have hfun :
      (fun w : ℂ => ∫ t : ℝ,
        realHermiteGenerating (t + x / 2) u *
          realHermiteGenerating (t - x / 2) w *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (ω * t : ℂ))) =
      fun w : ℂ => Complex.exp (u * w + z * u - star z * w) * E := by
    funext w
    exact realHermiteGenerating_ambiguity_integral_independent_kernel x ω u w
  rw [hfun]
  have hu : HasDerivAt (fun w : ℂ => u * w) u w0 := by
    simpa only [id_eq, mul_one] using HasDerivAt.const_mul u (hasDerivAt_id w0)
  have hz : HasDerivAt (fun w : ℂ => star z * w) (star z) w0 := by
    simpa only [id_eq, mul_one] using HasDerivAt.const_mul (star z) (hasDerivAt_id w0)
  have hlin := (hu.add_const (z * u)).sub hz
  exact (hlin.cexp.mul_const E).congr_deriv
    (congrArg (fun value : ℂ => value * E) (mul_comm _ _))
end DimdPolyLEAN
