-- Prove2me | solution 1 for DimdPolyLEAN.realHermite1D_zero_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:33.941774+00:00
-- url     : https://prove2.me/submissions/6cabace2-2f20-4ee7-ae75-81c4e0764cd0

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
public import Theorems.Thm_DimdPolyLEAN_realHermite1D_zero
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
private lemma neg_ofReal_sq_div_two_re (t : ℝ) :
    (-(↑t ^ 2 / 2) : ℂ).re = -(t ^ (2 : ℕ)) / 2 := by
  norm_num [Complex.div_re]
  rw [pow_two]
  simp [Complex.mul_re]
  ring
private lemma real_exp_neg_sq_eq_sq (t : ℝ) :
    Real.exp (-(t ^ (2 : ℕ))) = Real.exp (-(t ^ (2 : ℕ)) / 2) ^ (2 : ℕ) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring
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
theorem _root_.solution :
    MemLp (realHermite1D 0) 2 (volume : Measure ℝ) := by
  have hfun : realHermite1D 0 = (fun t : ℝ =>
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(((t : ℂ) ^ 2) / 2)))) := by
    funext t
    simp [realHermite1D_zero, realHermiteGenerating]
  rw [hfun]
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm ?_).2 ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · have hbase : Integrable (fun t : ℝ => Real.exp (-1 * t ^ (2 : ℝ))) := by
      simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) zero_lt_one
    have hbase_nat : Integrable (fun t : ℝ => Real.exp (-(t ^ (2 : ℕ)))) := by
      simp_all only [one_div, Real.rpow_ofNat, neg_mul, one_mul]
    refine (hbase_nat.const_mul
      (‖((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)‖ ^ (2 : ℕ))).congr ?_
    filter_upwards with t
    rw [norm_mul, Complex.norm_exp]
    rw [neg_ofReal_sq_div_two_re t]
    rw [real_exp_neg_sq_eq_sq t]
    ring
end DimdPolyLEAN
