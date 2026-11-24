-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_ambiguity_integral_linear_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:43.301999+00:00
-- url     : https://prove2.me/submissions/5d777323-db9e-4ee5-b136-4b0e35d34816

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_ambiguity_integral_raw
section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
private lemma sqrtTwoC_sq : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    (x ω : ℝ) (u v : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating (t + x / 2) u *
        realHermiteGenerating (t - x / 2) v *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (-(((x : ℂ) ^ 2 + (2 * Real.pi : ℂ) ^ 2 * (ω : ℂ) ^ 2) / 4)) *
        Complex.exp
          (((Real.sqrt 2 : ℂ) * (x : ℂ) / 2 -
              (Real.sqrt 2 : ℂ) * (Real.pi : ℂ) * Complex.I * (ω : ℂ)) * u -
            ((Real.sqrt 2 : ℂ) * (x : ℂ) / 2 +
              (Real.sqrt 2 : ℂ) * (Real.pi : ℂ) * Complex.I * (ω : ℂ)) * v +
            u * v) := by
  rw [realHermiteGenerating_ambiguity_integral_raw, ← Complex.exp_add]
  congr 1
  ring_nf
  rw [sqrtTwoC_sq, Complex.I_sq]
  ring
end DimdPolyLEAN
