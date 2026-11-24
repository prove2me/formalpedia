-- Prove2me | solution 1 for DimdPolyLEAN.exact_modulus_recovery_skappa_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:34.6798+00:00
-- url     : https://prove2.me/submissions/354621b5-2fe4-47b0-a05d-215f5ab6844c

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
public import Theorems.Thm_DimdPolyLEAN_ae_modulus_to_pointwise_modulus
public import Theorems.Thm_DimdPolyLEAN_ae_modulus_to_ambiguity_eq
public import Theorems.Thm_DimdPolyLEAN_ambiguity_eq_to_skappa_phase
public import Theorems.Thm_DimdPolyLEAN_coeff_recovery
public import Theorems.Thm_DimdPolyLEAN_toL2_eq_of_toFun_eq
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
private theorem skappa_eq_zero_of_coeff_zero_exact_wip
    {d : Nat} {kappa : MultiIndex d} {U : Skappa d kappa}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = 0) :
    U = 0 := by
  apply skappa_ext_coeff_exact_wip
  intro alpha
  rw [hcoeff alpha]
  change (0 : ℂ) = (0 : Skappa d kappa).coeff alpha
  rfl
private theorem toFun_zero_exact_wip
    {d : Nat} (kappa : MultiIndex d) :
    toFun kappa (0 : Skappa d kappa) = 0 := by
  ext z
  unfold toFun coeffSkappa
  change (∑' alpha : Idx d, (0 : ℂ) * Phi kappa alpha z) = 0
  simp
private theorem skappa_eq_zero_of_toFun_zero_exact_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) {U : Skappa d kappa}
    (hU : ∀ z, toFun kappa U z = 0) :
    U = 0 := by
  apply skappa_eq_zero_of_coeff_zero_exact_wip
  intro beta
  have hL2 : toL2 kappa U = toL2 kappa (0 : Skappa d kappa) := by
    exact toL2_eq_of_toFun_eq hd (fun z => by
      rw [hU z, toFun_zero_exact_wip kappa]
      rfl)
  calc
    coeffSkappa U beta = inner ℂ (PhiL2 kappa beta) (toL2 kappa U) := coeff_recovery hd kappa U beta
    _ = inner ℂ (PhiL2 kappa beta) (toL2 kappa (0 : Skappa d kappa)) := by rw [hL2]
    _ = coeffSkappa (0 : Skappa d kappa) beta :=
      (coeff_recovery hd kappa (0 : Skappa d kappa) beta).symm
    _ = 0 := rfl
private theorem coeff_eq_zero_of_self_kernel_zero_exact_wip {z : ℂ}
    (h : z * star z = 0) :
    z = 0 := by
  simp_all only [RCLike.star_def, mul_eq_zero, map_eq_zero, or_self]
private theorem norm_eq_of_self_kernel_eq_exact_wip {x y : ℂ}
    (h : x * star x = y * star y) :
    ‖x‖ = ‖y‖ := by
  have hmul_norm : ‖x‖ * ‖x‖ = ‖y‖ * ‖y‖ := by simpa [norm_mul, norm_star] using congrArg norm h
  have hsq : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by simpa [sq] using hmul_norm
  simp_all only [RCLike.star_def, norm_nonneg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    pow_left_inj₀]
private theorem scalar_multiple_of_coeff_kernel_exact_wip
    {d : Nat} {kappa : MultiIndex d} {U V : Skappa d kappa}
    (hker : ∀ alpha beta,
      coeffSkappa V alpha * star (coeffSkappa V beta) =
        coeffSkappa U alpha * star (coeffSkappa U beta)) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ V = w • U := by
  by_cases hU_zero : U = 0
  · have hV_coeff_zero : ∀ alpha, coeffSkappa V alpha = 0 := by
      intro alpha
      have hU_alpha_zero : coeffSkappa U alpha = 0 := by
        rw [hU_zero]
        rfl
      have hself : coeffSkappa V alpha * star (coeffSkappa V alpha) = 0 := by
        simp_all only [RCLike.star_def, map_zero, mul_zero]
      exact coeff_eq_zero_of_self_kernel_zero_exact_wip hself
    have hV_zero : V = 0 := skappa_eq_zero_of_coeff_zero_exact_wip hV_coeff_zero
    refine ⟨1, by norm_num, ?_⟩
    rw [hU_zero, hV_zero]
    apply skappa_ext_coeff_exact_wip
    intro alpha
    change (0 : ℂ) = (1 : ℂ) * 0
    simp
  · have hU_coeff_nonzero : ∃ alpha0, coeffSkappa U alpha0 ≠ 0 := by
      by_contra hnone
      have hzero : ∀ alpha, coeffSkappa U alpha = 0 := by
        simp_all only [RCLike.star_def, ne_eq, not_exists, Decidable.not_not, implies_true]
      exact hU_zero (skappa_eq_zero_of_coeff_zero_exact_wip hzero)
    rcases hU_coeff_nonzero with ⟨alpha0, hU0⟩
    let u0 : ℂ := coeffSkappa U alpha0
    let v0 : ℂ := coeffSkappa V alpha0
    let w : ℂ := v0 / u0
    have hnorm_eq : ‖v0‖ = ‖u0‖ := by
      dsimp [u0, v0]
      exact norm_eq_of_self_kernel_eq_exact_wip (hker alpha0 alpha0)
    have hu0_ne : u0 ≠ 0 := by exact hU0
    have hu0_norm_ne : ‖u0‖ ≠ 0 := norm_ne_zero_iff.mpr hu0_ne
    have hw_norm : ‖w‖ = 1 := by
      calc
        ‖w‖ = ‖v0‖ / ‖u0‖ := by simp [w]
        _ = ‖u0‖ / ‖u0‖ := by rw [hnorm_eq]
        _ = 1 := div_self hu0_norm_ne
    have hv0_eq : v0 = w * u0 := by
      dsimp [w]
      exact (div_mul_cancel₀ v0 hu0_ne).symm
    have hcoeff : ∀ alpha, coeffSkappa V alpha = w * coeffSkappa U alpha := by
      intro alpha
      let u : ℂ := coeffSkappa U alpha
      let v : ℂ := coeffSkappa V alpha
      have hrel : v * star v0 = u * star u0 := by
        dsimp [u, v, u0, v0]
        exact hker alpha alpha0
      have hstar_v0 : star v0 = star w * star u0 := by
        simp_all only [RCLike.star_def, ne_eq, Complex.norm_mul, one_mul, norm_eq_zero,
          not_false_eq_true, star_mul']
      have hcancel : v * star w = u := by
        apply mul_right_cancel₀ (star_ne_zero.mpr hu0_ne)
        calc
          (v * star w) * star u0 = v * (star w * star u0) := by ring
          _ = v * star v0 := by rw [← hstar_v0]
          _ = u * star u0 := hrel
      have hw_conj : w * star w = 1 := by simpa [hw_norm] using (RCLike.mul_conj w)
      have hstarw_mul_w : star w * w = 1 := by simpa [mul_comm] using hw_conj
      calc
        coeffSkappa V alpha = v := rfl
        _ = v * (star w * w) := by rw [hstarw_mul_w, mul_one]
        _ = (v * star w) * w := by ring
        _ = u * w := by rw [hcancel]
        _ = w * u := by ring
        _ = w * coeffSkappa U alpha := rfl
    refine ⟨w, hw_norm, ?_⟩
    apply skappa_ext_coeff_exact_wip
    intro alpha
    exact hcoeff alpha
private theorem coeff_kernel_of_scalar_multiple_exact_wip
    {d : Nat} {kappa : MultiIndex d} {U V : Skappa d kappa} {w : ℂ}
    (hw : ‖w‖ = 1) (hVU : V = w • U) :
    ∀ alpha beta,
      coeffSkappa V alpha * star (coeffSkappa V beta) =
        coeffSkappa U alpha * star (coeffSkappa U beta) := by
  intro alpha beta
  rw [hVU]
  change (w * coeffSkappa U alpha) * star (w * coeffSkappa U beta) =
    coeffSkappa U alpha * star (coeffSkappa U beta)
  have hw_conj : w * star w = 1 := by simpa [hw] using (RCLike.mul_conj w)
  calc
    (w * coeffSkappa U alpha) * star (w * coeffSkappa U beta) =
        (w * star w) * (coeffSkappa U alpha * star (coeffSkappa U beta)) := by
          rw [star_mul]
          ring
    _ = coeffSkappa U alpha * star (coeffSkappa U beta) := by
          simp_all only [RCLike.star_def, one_mul]
private theorem coeff_kernel_of_exact_modulus_recovery_skappa_ae_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Skappa d kappa}
    (hmod :
      (fun z => ‖toFun kappa U z‖) =ᵐ[gammaD d]
        fun z => ‖toFun kappa V z‖) :
    ∀ alpha beta,
      coeffSkappa V alpha * star (coeffSkappa V beta) =
        coeffSkappa U alpha * star (coeffSkappa U beta) := by
  rcases ambiguity_eq_to_skappa_phase hd kappa
      (ae_modulus_to_ambiguity_eq hd kappa hmod) with ⟨w, hw, hVU⟩
  exact coeff_kernel_of_scalar_multiple_exact_wip hw hVU
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
    (hmod :
      (fun z => ‖toFun kappa U z‖) =ᵐ[gammaD d]
        fun z => ‖toFun kappa V z‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ V = w • U := by
  have hpoint := ae_modulus_to_pointwise_modulus hd kappa hmod
  by_cases hU_zero : U = 0
  · have hV_toFun_zero : ∀ z, toFun kappa V z = 0 := by
      intro z
      have hz_norm : ‖toFun kappa V z‖ = 0 := by
        simpa [hU_zero, toFun_zero_exact_wip] using (hpoint z).symm
      exact norm_eq_zero.mp hz_norm
    have hV_zero : V = 0 :=
      skappa_eq_zero_of_toFun_zero_exact_wip hd kappa hV_toFun_zero
    refine ⟨1, by norm_num, ?_⟩
    rw [hU_zero, hV_zero]
    apply skappa_ext_coeff_exact_wip
    intro alpha
    change (0 : ℂ) = (1 : ℂ) * 0
    simp
  by_cases hV_zero : V = 0
  · have hU_toFun_zero : ∀ z, toFun kappa U z = 0 := by
      intro z
      have hz_norm : ‖toFun kappa U z‖ = 0 := by
        simpa [hV_zero, toFun_zero_exact_wip] using hpoint z
      exact norm_eq_zero.mp hz_norm
    exact False.elim
      (hU_zero (skappa_eq_zero_of_toFun_zero_exact_wip hd kappa hU_toFun_zero))
  exact scalar_multiple_of_coeff_kernel_exact_wip
    (coeff_kernel_of_exact_modulus_recovery_skappa_ae_wip hd kappa hmod)
end DimdPolyLEAN
