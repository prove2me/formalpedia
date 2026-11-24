-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_integral_shift_mul_modulated_completed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:21.896465+00:00
-- url     : https://prove2.me/submissions/be4044d8-8e55-4c50-b465-ae06a463a2ee

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_stft_integral_raw

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    (u v : ℂ) (x ω : ℝ) :
    (∫ t : ℝ,
      realHermiteGenerating t u * realHermiteGenerating (t - x) v *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        ((-((x : ℂ) ^ 2) / 2 - (Real.sqrt 2 : ℂ) * (x : ℂ) * v -
            (u ^ 2 + v ^ 2) / 2) +
          (((x : ℂ) + (Real.sqrt 2 : ℂ) * (u + v) -
              (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2) / 4) :=
  realHermiteGenerating_stft_integral_raw x ω u v
end DimdPolyLEAN
