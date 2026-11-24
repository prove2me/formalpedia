-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_ambiguity_integral_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:36.581042+00:00
-- url     : https://prove2.me/submissions/dcee491d-811a-4282-86a8-b60a2f42910b

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
theorem _root_.solution
    (x ω : ℝ) (u v : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating (t + x / 2) u *
        realHermiteGenerating (t - x / 2) v *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (-((x : ℂ) ^ 2) / 4 +
          (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
          (Real.sqrt 2 : ℂ) * (x : ℂ) * v / 2 -
          (u ^ 2 + v ^ 2) / 2 +
          (((Real.sqrt 2 : ℂ) * (u + v) -
              (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2) / 4) := by
  unfold realHermiteGenerating
  let a : ℂ := ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)
  let b : ℂ :=
    (Real.sqrt 2 : ℂ) * (u + v) -
      (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let c : ℂ :=
    -((x : ℂ) ^ 2) / 4 +
      (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
      (Real.sqrt 2 : ℂ) * (x : ℂ) * v / 2 -
      (u ^ 2 + v ^ 2) / 2
  change (∫ t : ℝ,
      a * Complex.exp
          (-((((t + x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t + x / 2 : ℝ) : ℂ) * u -
            u ^ 2 / 2) *
        (a * Complex.exp
          (-((((t - x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t - x / 2 : ℝ) : ℂ) * v -
            v ^ 2 / 2)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (-((x : ℂ) ^ 2) / 4 +
          (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
          (Real.sqrt 2 : ℂ) * (x : ℂ) * v / 2 -
          (u ^ 2 + v ^ 2) / 2 +
          (((Real.sqrt 2 : ℂ) * (u + v) -
              (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2) / 4)
  have hquad : ∀ t : ℝ,
      a * Complex.exp
          (-((((t + x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t + x / 2 : ℝ) : ℂ) * u -
            u ^ 2 / 2) *
        (a * Complex.exp
          (-((((t - x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t - x / 2 : ℝ) : ℂ) * v -
            v ^ 2 / 2)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
      (a * a) * Complex.exp (-(1 : ℂ) * (t : ℂ) ^ 2 + b * (t : ℂ) + c) := by
    intro t
    have hplus : (((t + x / 2 : ℝ) : ℂ)) = (t : ℂ) + (x : ℂ) / 2 := by norm_num
    have hminus : (((t - x / 2 : ℝ) : ℂ)) = (t : ℂ) - (x : ℂ) / 2 := by norm_num
    have hsum :
        (-((((t + x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t + x / 2 : ℝ) : ℂ) * u -
            u ^ 2 / 2) +
          (-((((t - x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t - x / 2 : ℝ) : ℂ) * v -
            v ^ 2 / 2) +
          (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
        -(1 : ℂ) * (t : ℂ) ^ 2 + b * (t : ℂ) + c := by
      simp only [b, c]
      rw [hplus, hminus]
      ring_nf
    rw [← hsum]
    calc
      a * Complex.exp
          (-((((t + x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t + x / 2 : ℝ) : ℂ) * u -
            u ^ 2 / 2) *
        (a * Complex.exp
          (-((((t - x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t - x / 2 : ℝ) : ℂ) * v -
            v ^ 2 / 2)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
          (a * a) *
            (Complex.exp
              (-((((t + x / 2 : ℝ) : ℂ) ^ 2) / 2) +
                (Real.sqrt 2 : ℂ) * ((t + x / 2 : ℝ) : ℂ) * u -
                u ^ 2 / 2) *
              Complex.exp
                (-((((t - x / 2 : ℝ) : ℂ) ^ 2) / 2) +
                  (Real.sqrt 2 : ℂ) * ((t - x / 2 : ℝ) : ℂ) * v -
                  v ^ 2 / 2) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) := by ring
      _ = (a * a) *
            Complex.exp
              ((-((((t + x / 2 : ℝ) : ℂ) ^ 2) / 2) +
                  (Real.sqrt 2 : ℂ) * ((t + x / 2 : ℝ) : ℂ) * u -
                  u ^ 2 / 2) +
                (-((((t - x / 2 : ℝ) : ℂ) ^ 2) / 2) +
                  (Real.sqrt 2 : ℂ) * ((t - x / 2 : ℝ) : ℂ) * v -
                  v ^ 2 / 2) +
                (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) := by
            rw [← Complex.exp_add, ← Complex.exp_add]
  simp_rw [hquad]
  rw [MeasureTheory.integral_const_mul]
  simpa only [a, b, c, sq] using integral_normalized_cexp_quadratic b c
end DimdPolyLEAN
