-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_integral_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:18:24.442245+00:00
-- url     : https://prove2.me/submissions/f3aff5a4-f522-47b3-95f7-883511d7d037

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


section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
private lemma sqrtTwoC_sq : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
private lemma piPow_quarter_sq_mul_half :
    ((↑(Real.pi ^ (-1 / 4 : ℝ)) : ℂ) ^ 2 * ((↑Real.pi : ℂ) ^ (1 / 2 : ℂ))) = 1 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (le_of_lt Real.pi_pos) (1 / 2 : ℝ)]
  have hpi_real :
      (Real.pi ^ (-1 / 4 : ℝ)) ^ 2 * Real.pi ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt Real.pi_pos),
      ← Real.rpow_add Real.pi_pos]
    norm_num
  exact_mod_cast hpi_real
private lemma integral_normalized_cexp_quadratic (b c : ℂ) :
    (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) ^ 2) *
        (∫ t : ℝ, Complex.exp (-(1 : ℂ) * (t : ℂ) ^ 2 + b * (t : ℂ) + c)) =
      Complex.exp (c + b ^ 2 / 4) := by
  rw [integral_cexp_quadratic (by norm_num : (-1 : ℂ).re < 0)]
  simp only [neg_neg, div_one, mul_neg, mul_one, div_neg, sub_neg_eq_add]
  rw [← mul_assoc, show -(1 / 4 : ℝ) = -1 / 4 by ring,
    piPow_quarter_sq_mul_half, one_mul]
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
theorem _root_.solution (u w : ℂ) :
    (∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) =
      Complex.exp (u * w) := by
  unfold realHermiteGenerating
  let a : ℂ := ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)
  let b : ℂ := (Real.sqrt 2 : ℂ) * (u + w)
  let c : ℂ := -(u ^ 2 + w ^ 2) / 2
  change (∫ t : ℝ,
      a * Complex.exp (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) *
          (t : ℂ) * u - u ^ 2 / 2) *
        (a * Complex.exp (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) *
          (t : ℂ) * w - w ^ 2 / 2))) =
      Complex.exp (u * w)
  have hquad : ∀ t : ℝ,
      a * Complex.exp (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) *
          (t : ℂ) * u - u ^ 2 / 2) *
        (a * Complex.exp (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) *
          (t : ℂ) * w - w ^ 2 / 2)) =
      (a * a) * Complex.exp (-(1 : ℂ) * (t : ℂ) ^ 2 + b * (t : ℂ) + c) := by
    intro t
    have hsum :
        (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * u - u ^ 2 / 2) +
            (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * w -
              w ^ 2 / 2) =
          -(1 : ℂ) * (t : ℂ) ^ 2 + b * (t : ℂ) + c := by
      simp only [b, c]
      ring_nf
    rw [← hsum, Complex.exp_add]
    ring
  simp_rw [hquad]
  rw [MeasureTheory.integral_const_mul]
  rw [← sq, integral_normalized_cexp_quadratic]
  congr 1
  dsimp [b, c]
  ring_nf
  rw [sqrtTwoC_sq]
  ring
end DimdPolyLEAN
