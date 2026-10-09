-- Prove2me | solution 1 for ConnesGreen.canonical_finite_certificate_complete_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T00:20:35.676708+00:00
-- url     : https://prove2.me/submissions/1b801d21-be43-4944-bcc1-9a40e53141ea

import Theorems.Thm_WeilDefect_MarkerStability_regularized_covariance_le_iff_selected_correction
import Definitions.Def_ConnesGreen_finite_selected_correction
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ContinuousLinearMap
private theorem regularization_positive_helper
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (P : K →L[ℂ] H) (δ : ℝ) (hδ : 0 < δ) :
    IsStrictlyPositive (P ∘L P.adjoint + δ • 1) :=
  IsStrictlyPositive.nonneg_add
    ((ContinuousLinearMap.nonneg_iff_isPositive (f := P ∘L P.adjoint)).mpr
      (isPositive_self_comp_adjoint P)) (isStrictlyPositive_one.smul hδ)


private theorem covariance_quadratic_helper
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (N : K →L[ℂ] H) :
    N ∘L N.adjoint ≤ A ↔ ∀ x : H, ‖N.adjoint x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ := by
  have hs := hA.sub (ContinuousLinearMap.isPositive_self_comp_adjoint N).isSelfAdjoint
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_def']
  simp only [hs, true_and]
  apply forall_congr'
  intro x
  have he := N.adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint] at he
  change (0 ≤ RCLike.re ⟪(A - N ∘L N.adjoint) x, x⟫_ℂ) ↔ _
  simp only [sub_apply, inner_sub_left, map_sub]
  rw [← he]
  exact sub_nonneg

namespace ConnesGreen
theorem canonical_finite_positive_analysis_energy (t : ℝ) (F : Finset CriticalZeros)
    (x : Physical t) :
    ‖(canonicalFinitePositiveSynthesis t F).adjoint x‖ ^ 2 =
      ∑ ρ ∈ F, ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2 := by
  rw [canonicalFinitePositiveSynthesis, columnSynthesis_adjoint_norm_sq]
  exact Finset.tsum_subtype F (fun ρ : CriticalZeros =>
    ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2)

theorem canonical_finite_positive_coefficient_strictPositive (t : ℝ)
    (F : Finset CriticalZeros) (δ : ℝ) (hδ : 0 < δ) :
    IsStrictlyPositive ((canonicalFinitePositiveSynthesis t F).adjoint ∘L
      canonicalFinitePositiveSynthesis t F + δ • 1) := by
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    regularization_positive_helper
      (canonicalFinitePositiveSynthesis t F).adjoint δ hδ

theorem canonical_finite_positive_covariance_quadratic (t : ℝ)
    (F : Finset CriticalZeros) (δ : ℝ) (x : Physical t) :
    RCLike.re ⟪((canonicalFinitePositiveSynthesis t F ∘L
      (canonicalFinitePositiveSynthesis t F).adjoint) + δ • 1) x, x⟫_ℂ =
      (∑ ρ ∈ F, ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2) + δ * ‖x‖ ^ 2 := by
  have hp := (canonicalFinitePositiveSynthesis t F).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint] at hp
  have hd : RCLike.re ⟪δ • x, x⟫_ℂ = δ * ‖x‖ ^ 2 := by
    change RCLike.re ⟪(δ : ℂ) • x, x⟫_ℂ = _
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
    change (star (δ : ℂ) * (‖x‖ : ℂ) ^ 2).re = _
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, inner_add_left, map_add, hd]
  rw [← hp, canonical_finite_positive_analysis_energy]

theorem canonical_finite_selected_correction_iff (t : ℝ) (ht : 0 < t)
    (S F : Finset CriticalZeros) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ canonicalFiniteSelectedCorrection t ht S F δ ↔
    ∀ x : Physical t, ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 ≤
      (∑ ρ ∈ F, ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2) + δ * ‖x‖ ^ 2 := by
  have hA := regularization_positive_helper
    (canonicalFinitePositiveSynthesis t F) δ hδ
  have hs := ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp hA.nonneg).isSelfAdjoint
  unfold canonicalFiniteSelectedCorrection
  rw [← WeilDefect.MarkerStability.regularized_covariance_le_iff_selected_correction _ _ δ hδ,
    covariance_quadratic_helper _ hs]
  simp only [canonical_finite_positive_covariance_quadratic]

end ConnesGreen

open Filter
namespace ConnesGreen
theorem canonical_positive_tail_cutoff (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : Finset CriticalZeros, S ⊆ F ∧ (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) < δ := by
  let p := positiveGreenColumn (fun ρ => sourceEmbed t (actualGreenSource ρ))
  have hs : Summable (fun ρ => ‖p ρ‖ ^ 2) := (canonical_actor_columns_summable t ht).1
  obtain ⟨F₀, hF₀⟩ := eventually_atTop.mp
    ((tendsto_order.mp (tendsto_tsum_compl_atTop_zero (fun ρ => ‖p ρ‖ ^ 2))).2 δ hδ)
  let G := F₀ ∪ S
  let F := G ∪ G.image reflectedZero
  refine ⟨F, Finset.subset_union_right.trans Finset.subset_union_left, ?_, ?_⟩
  · intro ρ hρ
    rcases Finset.mem_union.mp hρ with hρ | hρ
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hρ)
    · obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hρ
      rw [reflectedZero_involutive]
      exact Finset.mem_union_left _ hτ
  · exact hF₀ F (Finset.subset_union_left.trans Finset.subset_union_left)
theorem canonical_finite_certificate_of_enlargement
    (t : ℝ) (ht : 0 < t) (S F G : Finset CriticalZeros)
    (δ η : ℝ) (hδ : 0 < δ) (hFG : F ⊆ G) (hδη : δ ≤ η)
    (hF : 0 ≤ canonicalFiniteSelectedCorrection t ht S F δ) :
    0 ≤ canonicalFiniteSelectedCorrection t ht S G η := by
  apply (canonical_finite_selected_correction_iff t ht S G η
    (lt_of_lt_of_le hδ hδη)).mpr
  intro x
  have hx := (canonical_finite_selected_correction_iff t ht S F δ hδ).mp hF x
  have hm : (∑ ρ ∈ F,
      ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2) ≤
      ∑ ρ ∈ G,
        ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hFG (fun _ _ _ => sq_nonneg _)
  exact hx.trans (add_le_add hm (mul_le_mul_of_nonneg_right hδη (sq_nonneg ‖x‖)))

end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hF : 0 ≤ canonicalFiniteSelectedCorrection t ht S F δ) :
    ∃ G : Finset CriticalZeros, F ⊆ G ∧ S ⊆ G ∧
      (∀ ρ ∈ G, reflectedZero ρ ∈ G) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ G},
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) < ε ∧
      0 ≤ canonicalFiniteSelectedCorrection t ht S G δ := by
  obtain ⟨G, hG, hclosed, htail⟩ := canonical_positive_tail_cutoff t ht (F ∪ S) ε hε
  have hFG : F ⊆ G := Finset.subset_union_left.trans hG
  have hSG : S ⊆ G := Finset.subset_union_right.trans hG
  exact ⟨G, hFG, hSG, hclosed, htail,
    canonical_finite_certificate_of_enlargement t ht S F G δ δ hδ hFG le_rfl hF⟩
