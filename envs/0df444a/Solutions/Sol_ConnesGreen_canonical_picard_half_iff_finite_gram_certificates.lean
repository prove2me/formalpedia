-- Prove2me | solution 1 for ConnesGreen.canonical_picard_half_iff_finite_gram_certificates
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T21:11:08.758708+00:00
-- url     : https://prove2.me/submissions/268bbab3-bb46-4e01-9bc5-766210b9fcf2

import Theorems.Thm_WeilDefect_MarkerStability_finite_gram_posSemidef_iff_nonnegative
import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_finite_positive_certificates
import Definitions.Def_ConnesGreen_finite_certificate_gram
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
namespace ConnesGreen
theorem canonical_selected_analysis_eq_finite_sum (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t) :
    ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 =
      ∑ ρ ∈ S, ‖⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2 := by
  rw [canonicalSelectedSynthesis, columnSynthesis_adjoint_norm_sq]
  exact Finset.tsum_subtype S (fun ρ : CriticalZeros =>
    ‖⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2)

theorem canonicalFiniteCertificateOperator_selfAdjoint
    (t : ℝ) (S F : Finset CriticalZeros) (δ : ℝ) :
    IsSelfAdjoint (canonicalFiniteCertificateOperator t S F δ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪canonicalFiniteCertificateOperator t S F δ x, y⟫_ℂ =
    ⟪x, canonicalFiniteCertificateOperator t S F δ y⟫_ℂ
  simp only [canonicalFiniteCertificateOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.sum_apply,
    inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, sum_inner, inner_sum,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, inner_smul_right,
    InnerProductSpace.inner_left_rankOne_apply, InnerProductSpace.inner_right_rankOne_apply,
    RCLike.conj_ofReal]

theorem canonicalFiniteCertificateOperator_quadratic (t : ℝ) (ht : 0 < t)
    (S F : Finset CriticalZeros) (δ : ℝ) (x : Physical t) :
    RCLike.re ⟪canonicalFiniteCertificateOperator t S F δ x, x⟫_ℂ =
      (∑ ρ ∈ F, ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2) -
        ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 + δ * ‖x‖ ^ 2 := by
  rw [canonical_selected_analysis_eq_finite_sum]
  have hr (v : Physical t) : RCLike.re ⟪InnerProductSpace.rankOne ℂ v v x, x⟫_ℂ =
      ‖⟪v, x⟫_ℂ‖ ^ 2 := by
    rw [InnerProductSpace.inner_left_rankOne_apply, ← inner_conj_symm x v]
    rw [RCLike.conj_mul]
    change ((‖⟪v, x⟫_ℂ‖ : ℂ) ^ 2).re = _
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  simp only [canonicalFiniteCertificateOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, inner_sub_left,
    inner_add_left, sum_inner, map_sub, map_add, map_sum, hr]
  have hd : RCLike.re ⟪(δ • (1 : Physical t →L[ℂ] Physical t)) x, x⟫_ℂ = δ * ‖x‖ ^ 2 := by
    change RCLike.re ⟪(δ : ℂ) • x, x⟫_ℂ = _
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
    change (star (δ : ℂ) * (‖x‖ : ℂ) ^ 2).re = _
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hd]
  ring

/-- PSD of the finite, possibly singular Gram matrix is exactly the original
all-vector finite certificate inequality. Its orthogonal complement costs δI. -/
theorem canonicalFiniteCertificateGram_posSemidef_iff (t : ℝ) (ht : 0 < t)
    (S F : Finset CriticalZeros) (δ : ℝ) (hδ : 0 ≤ δ) :
    (canonicalFiniteCertificateGram t S F δ).PosSemidef ↔
      ∀ x : Physical t, ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 ≤
        (∑ ρ ∈ F, ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2) +
          δ * ‖x‖ ^ 2 := by
  have hshell : ∀ z : Physical t,
      (∀ i, ⟪canonicalFiniteActorFamily t S F i, z⟫_ℂ = 0) →
      canonicalFiniteCertificateOperator t S F δ z = δ • z := by
    intro z hz
    have hp : ∀ ρ ∈ F, ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, z⟫_ℂ = 0 :=
      fun ρ hρ => hz (Sum.inl ⟨ρ, hρ⟩)
    have hn : ∀ ρ ∈ S, ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, z⟫_ℂ = 0 :=
      fun ρ hρ => hz (Sum.inr ⟨ρ, hρ⟩)
    simp only [canonicalFiniteCertificateOperator, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.sum_apply,
      InnerProductSpace.rankOne_apply]
    change δ • z + (∑ ρ ∈ F, ⟪positiveGreenColumn
      (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, z⟫_ℂ • _) -
      (∑ ρ ∈ S, ⟪negativeGreenColumn
      (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, z⟫_ℂ • _) = _
    have hpf : (∑ ρ ∈ F, ⟪positiveGreenColumn
        (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, z⟫_ℂ •
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) = 0 := by
      apply Finset.sum_eq_zero
      intro ρ hρ
      rw [hp ρ hρ, zero_smul]
    have hnf : (∑ ρ ∈ S, ⟪negativeGreenColumn
        (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, z⟫_ℂ •
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) = 0 := by
      apply Finset.sum_eq_zero
      intro ρ hρ
      rw [hn ρ hρ, zero_smul]
    rw [hpf, hnf, add_zero, sub_zero]
  unfold canonicalFiniteCertificateGram
  rw [
    WeilDefect.MarkerStability.finite_gram_posSemidef_iff_nonnegative _
      (canonicalFiniteCertificateOperator_selfAdjoint t S F δ) _ δ hδ hshell,
    ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
  change (IsSelfAdjoint (canonicalFiniteCertificateOperator t S F δ) ∧
    ∀ x, 0 ≤ RCLike.re ⟪canonicalFiniteCertificateOperator t S F δ x, x⟫_ℂ) ↔ _
  simp only [canonicalFiniteCertificateOperator_selfAdjoint, true_and,
    canonicalFiniteCertificateOperator_quadratic t ht S F δ]
  exact forall_congr' fun x => by constructor <;> intro h <;> linarith


end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) ↔
    ∀ δ : ℝ, 0 < δ → ∃ F : Finset CriticalZeros,
      S ⊆ F ∧ (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) < δ ∧
      (canonicalFiniteCertificateGram t S F δ).PosSemidef := by
  rw [canonical_picard_half_iff_finite_positive_certificates]
  apply forall_congr'
  intro δ
  apply imp_congr_right
  intro hδ
  apply exists_congr
  intro F
  rw [canonicalFiniteCertificateGram_posSemidef_iff t ht S F δ hδ.le]
