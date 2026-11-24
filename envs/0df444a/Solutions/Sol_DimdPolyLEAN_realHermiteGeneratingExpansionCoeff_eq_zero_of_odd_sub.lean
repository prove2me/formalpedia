-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:58.090063+00:00
-- url     : https://prove2.me/submissions/173b9506-e759-4ae4-9a8a-bc9cd50569fa

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
private theorem iteratedDeriv_cexp_neg_sq_div_two_zero_of_odd
    {n : ℕ} (hodd : Odd n) :
    iteratedDeriv n (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0 = 0 := by
  let q : ℂ → ℂ := fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)
  have hfun : (fun u : ℂ => q (-u)) = q := by
    funext u
    simp [q]
  have hder := iteratedDeriv_comp_neg n q (0 : ℂ)
  rw [hfun] at hder
  simp only [neg_zero] at hder
  have hneg : ((-1 : ℂ) ^ n) = -1 := by exact hodd.neg_one_pow
  rw [hneg, neg_smul, one_smul] at hder
  exact CharZero.neg_eq_self_iff.mp hder.symm
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
    {n k : ℕ} (hodd : Odd (n - k)) :
    realHermiteGeneratingExpansionCoeff n k = 0 := by
  simp [realHermiteGeneratingExpansionCoeff,
    iteratedDeriv_cexp_neg_sq_div_two_zero_of_odd hodd]
end DimdPolyLEAN
