-- Prove2me | solution 1 for DimdPolyLEAN.integral_real_pow_exp_neg_sq_of_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:12.376254+00:00
-- url     : https://prove2.me/submissions/254cf28e-d35f-4660-8756-4d2a042d0914

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
theorem _root_.solution
    {n : ℕ} (heven : Even n) :
    (∫ x : ℝ, x ^ n * Real.exp (-(x ^ (2 : ℕ)))) =
      Real.Gamma (((n : ℝ) + 1) / 2) := by
  have h_abs : (fun x : ℝ => x ^ n * Real.exp (-(x ^ (2 : ℕ)))) =
      fun x : ℝ => (fun y : ℝ => y ^ n * Real.exp (-(y ^ (2 : ℕ)))) |x| := by
    funext x
    simp [sq_abs, heven.pow_abs x]
  rw [h_abs]
  rw [show (∫ x : ℝ,
        (fun y : ℝ => y ^ n * Real.exp (-(y ^ (2 : ℕ)))) |x|) =
      2 * ∫ x in Set.Ioi (0 : ℝ),
        (fun y : ℝ => y ^ n * Real.exp (-(y ^ (2 : ℕ)))) x by
    simpa using
      (integral_comp_abs
        (f := fun y : ℝ => y ^ n * Real.exp (-(y ^ (2 : ℕ)))))]
  rw [show (∫ x in Set.Ioi (0 : ℝ),
      (fun y : ℝ => y ^ n * Real.exp (-(y ^ (2 : ℕ)))) x) =
      ∫ x in Set.Ioi (0 : ℝ), x ^ (n : ℝ) * Real.exp (-1 * x ^ (2 : ℝ)) by
    simp_all]
  rw [integral_rpow_mul_exp_neg_mul_rpow]
  · simp_all
  · norm_num
  · exact_mod_cast (show -1 < (n : ℤ) by omega)
  · norm_num
end DimdPolyLEAN
