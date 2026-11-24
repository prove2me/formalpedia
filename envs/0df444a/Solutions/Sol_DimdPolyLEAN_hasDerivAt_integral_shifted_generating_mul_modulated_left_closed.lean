-- Prove2me | solution 1 for DimdPolyLEAN.hasDerivAt_integral_shifted_generating_mul_modulated_left_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:22.858173+00:00
-- url     : https://prove2.me/submissions/dd709fd3-71a5-4d76-85dd-6bb70456f872

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
    (u0 w : ℂ) (x ω : ℝ) :
    HasDerivAt
      (fun u : ℂ => ∫ t : ℝ,
        realHermiteGenerating (t + x / 2) u *
          realHermiteGenerating (t - x / 2) w *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (ω * t : ℂ)))
      (((w +
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
          Complex.exp
            (u0 * w +
              (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * u0 -
                star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * w)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))))
      u0 := by
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  change HasDerivAt _
    (((w + z) * Complex.exp (u0 * w + z * u0 - star z * w)) * E) u0
  have hfun :
      (fun u : ℂ => ∫ t : ℝ,
        realHermiteGenerating (t + x / 2) u *
          realHermiteGenerating (t - x / 2) w *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (ω * t : ℂ))) =
      fun u : ℂ => Complex.exp (u * w + z * u - star z * w) * E := by
    funext u
    exact realHermiteGenerating_ambiguity_integral_independent_kernel x ω u w
  rw [hfun]
  have hw : HasDerivAt (fun u : ℂ => u * w) w u0 := by
    simpa only [id_eq, one_mul] using HasDerivAt.mul_const (hasDerivAt_id u0) w
  have hz : HasDerivAt (fun u : ℂ => z * u) z u0 := by
    simpa only [id_eq, mul_one] using HasDerivAt.const_mul z (hasDerivAt_id u0)
  have hlin := (hw.add hz).sub_const (star z * w)
  exact (hlin.cexp.mul_const E).congr_deriv
    (congrArg (fun value : ℂ => value * E) (mul_comm _ _))
end DimdPolyLEAN
