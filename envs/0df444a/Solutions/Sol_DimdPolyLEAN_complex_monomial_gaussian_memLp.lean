-- Prove2me | solution 1 for DimdPolyLEAN.complex_monomial_gaussian_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:40.393008+00:00
-- url     : https://prove2.me/submissions/1242a801-661e-409e-9f9a-1ea288d107a9

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
private lemma integrable_pow_mul_exp_neg_sq
    (n : ℕ) :
    Integrable (fun r : ℝ => r ^ n * Real.exp (-r ^ 2)) volume := by
  have hs : (-1 : ℝ) < (n : ℝ) := by exact_mod_cast (show -1 < (n : ℤ) by omega)
  have h := integrable_rpow_mul_exp_neg_mul_sq one_pos hs
  simp_all only [Real.rpow_natCast, neg_mul, one_mul]
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
    (k : ℕ) :
    MemLp (fun t : ℝ => (t : ℂ) ^ k *
      Complex.exp (-(((t : ℂ) ^ 2) / 2))) 2 (volume : Measure ℝ) := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm ?_).2 ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · have hbase :
        Integrable (fun t : ℝ => t ^ (2 * k) * Real.exp (-(t ^ (2 : ℕ)))) := by
      simpa [pow_two] using integrable_pow_mul_exp_neg_sq (2 * k)
    refine hbase.congr ?_
    filter_upwards with t
    simp only [norm_mul, norm_pow, Complex.norm_exp]
    rw [neg_ofReal_sq_div_two_re t]
    rw [real_exp_neg_sq_eq_sq t]
    rw [show t ^ (2 * k) = ‖(t : ℂ)‖ ^ (k * 2) by
      rw [show ‖(t : ℂ)‖ ^ (k * 2) = t ^ (k * 2) by
        rw [pow_mul, ← norm_pow, ← Complex.normSq_eq_norm_sq]
        simp [Complex.normSq_ofReal, ← Complex.ofReal_pow, pow_mul]
        ring_nf]
      ring_nf]
    rw [pow_mul]
    ring_nf
end DimdPolyLEAN
