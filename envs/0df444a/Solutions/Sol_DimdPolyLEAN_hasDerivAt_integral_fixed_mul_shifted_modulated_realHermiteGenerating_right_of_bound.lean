-- Prove2me | solution 1 for DimdPolyLEAN.hasDerivAt_integral_fixed_mul_shifted_modulated_realHermiteGenerating_right_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:00.430474+00:00
-- url     : https://prove2.me/submissions/6773f117-a62d-48e5-ad8a-d4348ac56014

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_hasDerivAt

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    (phi : ℝ → ℂ) (x ω : ℝ) (w0 : ℂ) {s : Set ℂ} {bound : ℝ → ℝ}
    (hs : s ∈ 𝓝 w0)
    (hF_meas : ∀ᶠ z in 𝓝 w0,
      AEStronglyMeasurable
        (fun t : ℝ =>
          (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))
        (volume : Measure ℝ))
    (hF_int : Integrable
      (fun t : ℝ =>
        (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ))
    (hF'_meas : AEStronglyMeasurable
      (fun t : ℝ =>
        (phi t *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ))
    (h_bound : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), ∀ z : ℂ, z ∈ s →
      ‖(phi t *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) z)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))‖ ≤
        bound t)
    (bound_integrable : Integrable bound (volume : Measure ℝ)) :
    HasDerivAt
      (fun z : ℂ => ∫ t : ℝ,
        (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (∫ t : ℝ,
        (phi t *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      w0 := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t =>
      (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ)))
    (F' := fun z t =>
      (phi t *
          (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
            realHermiteGenerating (t - (1 / 2 : ℝ) * x) z)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ)))
    (bound := bound) hs hF_meas hF_int hF'_meas h_bound bound_integrable ?_).2
  exact ae_of_all _ fun t z _ => by
    exact
      ((realHermiteGenerating_hasDerivAt (t - (1 / 2 : ℝ) * x) z).const_mul
        (phi t)).mul_const
          (Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
end DimdPolyLEAN
