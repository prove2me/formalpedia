-- Prove2me | solution 1 for DimdPolyLEAN.exact_modulus_recovery_pkappa
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:14.751432+00:00
-- url     : https://prove2.me/submissions/ef740d0d-5a02-49a6-a15e-966379eb4756

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
public import Theorems.Thm_DimdPolyLEAN_exact_modulus_recovery_skappa
public import Theorems.Thm_DimdPolyLEAN_coeff_ofPkappa
public import Theorems.Thm_DimdPolyLEAN_evalPkappa_zero
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
private theorem toFun_ofPkappa_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) :
    toFun kappa (ofPkappa kappa F) = evalPkappa kappa F := by
  let _ := hd
  ext z
  rw [toFun, evalPkappa, Finsupp.sum]
  have hzero :
      ∀ alpha ∉ F.support,
        coeffSkappa (ofPkappa kappa F) alpha * Phi kappa alpha z = 0 := by
    intro alpha halpha
    simp [coeffSkappa, ofPkappa, Finsupp.notMem_support_iff.mp halpha]
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [coeffSkappa, ofPkappa]
private theorem norm_sq_eq_sum_coeff_exact_wip
    {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) :
    ‖F‖ ^ 2 = Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) := by
  change (Real.sqrt (Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2))) ^ 2 = _
  rw [Real.sq_sqrt]
  positivity
private theorem pkappa_eq_zero_of_norm_sq_eq_zero_wip
    {d : Nat} {kappa : MultiIndex d} {F : Pkappa d kappa}
    (hF_norm_sq : ‖F‖ ^ 2 = 0) :
    F = 0 := by
  ext alpha
  by_cases hmem : alpha ∈ F.support
  · have hsum_zero :
        Finset.sum F.support (fun beta => ‖F beta‖ ^ 2) = 0 := by
      simpa [norm_sq_eq_sum_coeff_exact_wip F] using hF_norm_sq
    have hle :
        ‖F alpha‖ ^ 2 ≤ Finset.sum F.support (fun beta => ‖F beta‖ ^ 2) := by
      simpa using
        (Finset.single_le_sum
          (f := fun beta : Idx d => ‖F beta‖ ^ 2) (s := F.support) (a := alpha)
          (fun beta _ => by positivity) hmem)
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      Finsupp.mem_support_iff, sq_nonpos_iff, norm_eq_zero]
  · exact Finsupp.notMem_support_iff.mp hmem
private theorem pkappa_eq_zero_of_eval_zero_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {F : Pkappa d kappa} (hF_eval : ∀ z, evalPkappa kappa F z = 0) :
    F = 0 := by
  have hmass := evalPkappa_total_mass hd kappa F
  have hintegral_zero :
      (∫ z, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = 0 := by simp [hF_eval]
  have hnorm_sq : ‖F‖ ^ 2 = 0 := by linarith only [hmass, hintegral_zero]
  exact pkappa_eq_zero_of_norm_sq_eq_zero_wip hnorm_sq
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
    {U V : Pkappa d kappa}
    (hmod : ∀ z, ‖evalPkappa kappa U z‖ = ‖evalPkappa kappa V z‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ V = w • U := by
  let _ := hd
  by_cases hU_zero : U = 0
  · subst U
    have hV_eval : ∀ z, evalPkappa kappa V z = 0 := by
      intro z
      have hz : ‖evalPkappa kappa V z‖ = 0 := by
        simpa [evalPkappa_zero hd kappa] using (hmod z).symm
      exact norm_eq_zero.mp hz
    have hV_zero : V = 0 := pkappa_eq_zero_of_eval_zero_wip hd kappa hV_eval
    refine ⟨1, by norm_num, ?_⟩
    simp [hV_zero]
  by_cases hV_zero : V = 0
  · subst V
    have hU_eval : ∀ z, evalPkappa kappa U z = 0 := by
      intro z
      have hz : ‖evalPkappa kappa U z‖ = 0 := by simpa [evalPkappa_zero hd kappa] using hmod z
      exact norm_eq_zero.mp hz
    have hU_zero' : U = 0 := pkappa_eq_zero_of_eval_zero_wip hd kappa hU_eval
    exact False.elim (hU_zero hU_zero')
  have hmod' : ∀ z, ‖toFun kappa (ofPkappa kappa U) z‖ =
      ‖toFun kappa (ofPkappa kappa V) z‖ := by
    intro z
    simpa [toFun_ofPkappa_wip hd kappa U, toFun_ofPkappa_wip hd kappa V] using hmod z
  rcases exact_modulus_recovery_skappa hd kappa hmod' with ⟨w, hw, hVU⟩
  refine ⟨w, hw, ?_⟩
  ext alpha
  have hcoeff := congrArg (fun S : Skappa d kappa => coeffSkappa S alpha) hVU
  simp only [coeffSkappa] at hcoeff
  rw [show ((w • ofPkappa kappa U).coeff alpha) = w * (ofPkappa kappa U).coeff alpha from rfl]
    at hcoeff
  simpa [coeff_ofPkappa, hd, ofPkappa] using hcoeff
end DimdPolyLEAN
