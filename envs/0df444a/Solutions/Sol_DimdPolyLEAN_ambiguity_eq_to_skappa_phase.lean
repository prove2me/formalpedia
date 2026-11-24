-- Prove2me | solution 1 for DimdPolyLEAN.ambiguity_eq_to_skappa_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:56.214931+00:00
-- url     : https://prove2.me/submissions/0abb0826-22e4-496d-b2fa-3d6c8ac3c65f

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
public import Theorems.Thm_DimdPolyLEAN_bKappa_smul
public import Theorems.Thm_DimdPolyLEAN_bKappa_injective
public import Theorems.Thm_DimdPolyLEAN_bKappaRep_isL2Rep
public import Theorems.Thm_DimdPolyLEAN_rankOneRecoveryFromAmbiguity
public import Theorems.Thm_DimdPolyLEAN_lift_unimodular_phase_L2_to_Skappa
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
private theorem skappa_ext_coeff_exact_wip
    {d : Nat} {kappa : MultiIndex d} {U V : Skappa d kappa}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = coeffSkappa V alpha) :
    U = V := by
  cases U
  cases V
  simp only [coeffSkappa] at hcoeff
  congr
  funext alpha
  exact hcoeff alpha
private theorem bKappa_zero_exact_wip
    {d : Nat} (kappa : MultiIndex d) :
    bKappa kappa (0 : Skappa d kappa) = 0 := by
  have h := bKappa_smul kappa (0 : ℂ) (0 : Skappa d kappa)
  have hzero_smul : (0 : ℂ) • (0 : Skappa d kappa) = 0 := by
    apply skappa_ext_coeff_exact_wip
    intro alpha
    change (0 : ℂ) * 0 = 0
    simp
  simpa [hzero_smul] using h
private theorem skappa_eq_zero_of_bKappa_eq_zero_exact_wip
    {d : Nat} {kappa : MultiIndex d} {U : Skappa d kappa}
    (hU : bKappa kappa U = 0) :
    U = 0 := by
  apply bKappa_injective kappa
  rw [hU, bKappa_zero_exact_wip]
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
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Skappa d kappa}
    (hAmb : ∀ ξ,
      ambiguityRep (bKappa kappa U) (bKappa kappa U) ξ =
        ambiguityRep (bKappa kappa V) (bKappa kappa V) ξ) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ V = w • U := by
  let fRep := bKappaRep kappa U
  let gRep := bKappaRep kappa V
  have hf_rep : IsL2Rep (bKappa kappa U) fRep :=
    bKappaRep_isL2Rep kappa U
  have hg_rep : IsL2Rep (bKappa kappa V) gRep :=
    bKappaRep_isL2Rep kappa V
  rcases rankOneRecoveryFromAmbiguity hf_rep hg_rep hAmb with hzero | hphase
  · rcases hzero with ⟨hU_zero, hV_zero⟩
    have hU0 : U = 0 := skappa_eq_zero_of_bKappa_eq_zero_exact_wip hU_zero
    have hV0 : V = 0 := skappa_eq_zero_of_bKappa_eq_zero_exact_wip hV_zero
    refine ⟨1, by norm_num, ?_⟩
    rw [hU0, hV0]
    apply skappa_ext_coeff_exact_wip
    intro alpha
    change (0 : ℂ) = (1 : ℂ) * 0
    simp
  · rcases hphase with ⟨w, hw, hL2⟩
    exact ⟨w, hw, lift_unimodular_phase_L2_to_Skappa hd kappa hL2⟩
end DimdPolyLEAN
