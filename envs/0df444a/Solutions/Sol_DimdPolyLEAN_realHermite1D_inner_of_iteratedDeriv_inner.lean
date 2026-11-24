-- Prove2me | solution 1 for DimdPolyLEAN.realHermite1D_inner_of_iteratedDeriv_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:30.55119+00:00
-- url     : https://prove2.me/submissions/85733b82-8010-455f-b35c-e3992dbfce0d

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
theorem _root_.solution (n m : ℕ)
    (hderiv :
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating t) 0 *
          star (iteratedDeriv m (realHermiteGenerating t) 0)) =
        if n = m then (Nat.factorial n : ℂ) else 0) :
    (∫ t : ℝ, realHermite1D n t * star (realHermite1D m t)) =
      if n = m then 1 else 0 := by
  unfold realHermite1D
  let cn : ℂ := (Real.sqrt (Nat.factorial n : ℝ) : ℂ) / (Nat.factorial n : ℂ)
  let cm : ℂ := (Real.sqrt (Nat.factorial m : ℝ) : ℂ) / (Nat.factorial m : ℂ)
  change (∫ t : ℝ,
      (cn * iteratedDeriv n (realHermiteGenerating t) 0) *
        star (cm * iteratedDeriv m (realHermiteGenerating t) 0)) =
      if n = m then 1 else 0
  have hcm : star cm = cm := by simp [cm, Complex.conj_ofReal]
  have hcombine :
      (∫ t : ℝ,
          (cn * iteratedDeriv n (realHermiteGenerating t) 0) *
            star (cm * iteratedDeriv m (realHermiteGenerating t) 0)) =
        (cn * cm) * ∫ t : ℝ,
          iteratedDeriv n (realHermiteGenerating t) 0 *
            star (iteratedDeriv m (realHermiteGenerating t) 0) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [star_mul, hcm]
    ring
  rw [hcombine, hderiv]
  by_cases hnm : n = m
  · subst m
    have hnorm : (cn * cm) * (Nat.factorial n : ℂ) = 1 := by
      have hfac_pos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
      have hfac_ne : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hsqrt_ne : (Real.sqrt (Nat.factorial n : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 hfac_pos).ne'
      have hsqrt_sq :
          (Real.sqrt (Nat.factorial n : ℝ) : ℂ) ^ 2 = (Nat.factorial n : ℂ) := by
        norm_num [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hfac_pos)]
      simp only [cn, cm]
      rw [← hsqrt_sq]
      field_simp [hfac_ne, hsqrt_ne]
    simpa using hnorm
  · simp [hnm]
end DimdPolyLEAN
