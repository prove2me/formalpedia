-- Prove2me | solution 1 for DimdPolyLEAN.integral_real_sq_exp_neg_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:28.08693+00:00
-- url     : https://prove2.me/submissions/0e9574af-191a-40dd-8a6f-23d9b221f0d9

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



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution :
    (∫ x : ℝ, x ^ (2 : ℕ) * Real.exp (-(x ^ (2 : ℕ)))) = Real.sqrt Real.pi / 2 := by
  have h_abs : (fun x : ℝ => x ^ (2 : ℕ) * Real.exp (-(x ^ (2 : ℕ)))) =
      fun x : ℝ => (fun y : ℝ => y ^ (2 : ℕ) * Real.exp (-(y ^ (2 : ℕ)))) |x| := by
    simp_all only [sq_abs]
  rw [h_abs]
  rw [show (∫ x : ℝ, (fun y : ℝ => y ^ (2 : ℕ) * Real.exp (-(y ^ (2 : ℕ)))) |x|) =
      2 * ∫ x in Set.Ioi (0 : ℝ),
        (fun y : ℝ => y ^ (2 : ℕ) * Real.exp (-(y ^ (2 : ℕ)))) x by
    simpa using
      (integral_comp_abs
        (f := fun y : ℝ => y ^ (2 : ℕ) * Real.exp (-(y ^ (2 : ℕ)))))]
  rw [show (∫ x in Set.Ioi (0 : ℝ),
      (fun y : ℝ => y ^ (2 : ℕ) * Real.exp (-(y ^ (2 : ℕ)))) x) =
      ∫ x in Set.Ioi (0 : ℝ), x ^ (2 : ℝ) * Real.exp (-1 * x ^ (2 : ℝ)) by
    simp_all only [sq_abs, Real.rpow_ofNat, neg_mul, one_mul]]
  rw [integral_rpow_mul_exp_neg_mul_rpow]
  · rw [show ((2 : ℝ) + 1) / 2 = ((1 : ℕ) : ℝ) + 1 / 2 by norm_num]
    rw [Real.Gamma_nat_add_half]
    simp_all only [sq_abs, neg_add_rev, Real.one_rpow, one_div, one_mul, mul_one,
      Nat.add_one_sub_one, Nat.doubleFactorial.eq_2, Nat.cast_one, pow_one, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel_left₀]
  · norm_num
  · norm_num
  · norm_num
end DimdPolyLEAN
