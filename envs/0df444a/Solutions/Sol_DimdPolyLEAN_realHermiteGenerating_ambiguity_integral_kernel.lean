-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_ambiguity_integral_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:40.841094+00:00
-- url     : https://prove2.me/submissions/98c45372-1099-4ad3-a036-b3e5113c3cc9

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_ambiguity_integral_linear_form
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


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
private lemma star_sub_div_sqrtTwo (x ω : ℝ) :
    star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
        (Real.sqrt 2 : ℂ)) =
      ((x : ℂ) + (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
        (Real.sqrt 2 : ℂ) := by
  simp only [star_div₀, star_sub, RCLike.star_def, Complex.conj_ofReal, star_mul', star_ofNat,
    Complex.conj_I, mul_neg, neg_mul, sub_neg_eq_add]
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
    (x ω : ℝ) (u w : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating (t + x / 2) u *
        realHermiteGenerating (t - x / 2) w *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (u * w +
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * u -
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * w) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  rw [realHermiteGenerating_ambiguity_integral_linear_form, Complex.ofReal_exp,
    ← Complex.exp_add, star_sub_div_sqrtTwo]
  ring_nf
  rw [sqrtTwoC_inv]
  ring_nf
  rw [← Complex.exp_add]
  congr 1
  rw [show
      (((x ^ 2 * (-1 / 4) - Real.pi ^ 2 * ω ^ 2) : ℝ) : ℂ) =
        (x : ℂ) ^ 2 * (-1 / 4) - (Real.pi : ℂ) ^ 2 * (ω : ℂ) ^ 2 by
    norm_num [← Complex.ofReal_pow]]
  ring_nf
end DimdPolyLEAN
