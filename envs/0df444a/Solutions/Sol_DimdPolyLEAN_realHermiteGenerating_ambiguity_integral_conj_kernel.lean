-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_ambiguity_integral_conj_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:07.567154+00:00
-- url     : https://prove2.me/submissions/d5adcb3a-3cbf-4aba-b4f0-0fd6491fc181

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_ambiguity_integral_conj_raw
section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
private lemma sqrtTwoC_sq : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
private lemma sqrtTwoC_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
private lemma sqrtTwoC_inv : (Real.sqrt 2 : ℂ)⁻¹ = (Real.sqrt 2 : ℂ) / 2 := by
  field_simp [sqrtTwoC_ne]
  rw [sqrtTwoC_sq]
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
        star (realHermiteGenerating (t - x / 2) v) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (u * star v +
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * u -
          (((x : ℂ) + (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * star v) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  rw [realHermiteGenerating_ambiguity_integral_conj_raw, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  ring_nf
  rw [sqrtTwoC_inv]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by rw [pow_two, Complex.I_mul_I]]
  rw [sqrtTwoC_sq]
  rw [show
      (((x ^ 2 * (-1 / 4) - Real.pi ^ 2 * ω ^ 2) : ℝ) : ℂ) =
        (x : ℂ) ^ 2 * (-1 / 4) - (Real.pi : ℂ) ^ 2 * (ω : ℂ) ^ 2 by
    norm_num [← Complex.ofReal_pow]]
  ring_nf
end DimdPolyLEAN
