-- Prove2me | solution 1 for DimdPolyLEAN.hasDerivAt_integral_shifted_generating_mul_modulated_right_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:11.896325+00:00
-- url     : https://prove2.me/submissions/c6cf1a10-4727-45c2-b0e6-f79bd49781ba

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
public import Theorems.Thm_DimdPolyLEAN_hasDerivAt_integral_fixed_mul_shifted_modulated_realHermiteGenerating_right_of_bound

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    (u w0 : ℂ) (x ω : ℝ) {s : Set ℂ} {bound : ℝ → ℝ}
    (hs : s ∈ 𝓝 w0)
    (hF_meas : ∀ᶠ z in 𝓝 w0,
      AEStronglyMeasurable
        (fun t : ℝ =>
          (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ ω t : ℝ) : ℂ)))
        (volume : Measure ℝ))
    (hF_int : Integrable
      (fun t : ℝ =>
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
          realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ))
    (hF'_meas : AEStronglyMeasurable
      (fun t : ℝ =>
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ))
    (h_bound : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), ∀ z : ℂ, z ∈ s →
      ‖(realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) z)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))‖ ≤
        bound t)
    (bound_integrable : Integrable bound (volume : Measure ℝ)) :
    HasDerivAt
      (fun z : ℂ => ∫ t : ℝ,
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
          realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))
      (∫ t : ℝ,
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      w0 := by
  exact
    hasDerivAt_integral_fixed_mul_shifted_modulated_realHermiteGenerating_right_of_bound
      (phi := fun t : ℝ => realHermiteGenerating (t + (1 / 2 : ℝ) * x) u)
      (x := x) (ω := ω) (w0 := w0) (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound bound_integrable
end DimdPolyLEAN
