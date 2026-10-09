-- Prove2me | solution 1 for ConnesGreen.canonical_finite_certificate_neutral_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T04:19:05.398617+00:00
-- url     : https://prove2.me/submissions/83b53404-d7ab-4c5b-8e37-2430756096e7

import Definitions.Def_ConnesGreen_finite_selected_correction
import Theorems.Thm_WeilDefect_MarkerStability_regularized_covariance_le_iff_selected_correction
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability
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
theorem canonical_positive_analysis_finite_tail_bound (t : ℝ) (ht : 0 < t)
    (F : Finset CriticalZeros) (x : Physical t) :
    let p := positiveGreenColumn (fun ρ => sourceEmbed t (actualGreenSource ρ))
    0 ≤ ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
      ∑ ρ ∈ F, ‖⟪p ρ, x⟫_ℂ‖ ^ 2 ∧
    ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
      ∑ ρ ∈ F, ‖⟪p ρ, x⟫_ℂ‖ ^ 2 ≤
        (∑' ρ : {ρ : CriticalZeros // ρ ∉ F}, ‖p ρ.1‖ ^ 2) * ‖x‖ ^ 2 := by
  dsimp only
  let p := positiveGreenColumn (fun ρ => sourceEmbed t (actualGreenSource ρ))
  have hs : Summable (fun ρ => ‖p ρ‖ ^ 2) := (canonical_actor_columns_summable t ht).1
  have hb (ρ : CriticalZeros) : ‖⟪p ρ, x⟫_ℂ‖ ^ 2 ≤ ‖p ρ‖ ^ 2 * ‖x‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_inner_le_norm (𝕜 := ℂ) (p ρ) x) 2
  have ha : Summable (fun ρ => ‖⟪p ρ, x⟫_ℂ‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb (hs.mul_right (‖x‖ ^ 2))
  have he : ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
      ∑ ρ ∈ F, ‖⟪p ρ, x⟫_ℂ‖ ^ 2 =
      ∑' ρ : {ρ : CriticalZeros // ρ ∉ F}, ‖⟪p ρ.1, x⟫_ℂ‖ ^ 2 := by
    rw [canonicalPositiveSynthesis, columnSynthesis_adjoint_norm_sq,
      ← ha.sum_add_tsum_subtype_compl F]
    ring
  change 0 ≤ _ ∧ _ ≤ _
  rw [he]
  refine ⟨tsum_nonneg (fun _ => sq_nonneg _), ?_⟩
  have hsub := hs.comp_injective
    (Subtype.val_injective : Function.Injective (Subtype.val : {ρ : CriticalZeros // ρ ∉ F} → CriticalZeros))
  rw [← tsum_mul_right]
  exact (ha.comp_injective Subtype.val_injective).tsum_le_tsum (fun ρ => hb ρ.1)
    (hsub.mul_right (‖x‖ ^ 2))

end ConnesGreen

namespace ConnesGreen
theorem canonical_positive_analysis_tail_identity (t : ℝ) (ht : 0 < t)
    (F : Finset CriticalZeros) (x : Physical t) :
    ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
      (∑ ρ ∈ F, ‖⟪positiveGreenColumn
        (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2) =
      ∑' ρ : {ρ : CriticalZeros // ρ ∉ F}, ‖⟪positiveGreenColumn
        (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1, x⟫_ℂ‖ ^ 2 := by
  let p := positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ))
  have hs := (canonical_actor_columns_summable t ht).1
  have hb (ρ : CriticalZeros) : ‖⟪p ρ, x⟫_ℂ‖ ^ 2 ≤ ‖p ρ‖ ^ 2 * ‖x‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_inner_le_norm (𝕜 := ℂ) (p ρ) x) 2
  have ha : Summable (fun ρ => ‖⟪p ρ, x⟫_ℂ‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb (hs.mul_right (‖x‖ ^ 2))
  rw [canonicalPositiveSynthesis, columnSynthesis_adjoint_norm_sq,
    ← ha.sum_add_tsum_subtype_compl F]
  ring
end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) (hδ : 0 < δ)
    (hF : 0 ≤ canonicalFiniteSelectedCorrection t ht S F δ)
    (x : Physical t)
    (hneutral : ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 + δ * ‖x‖ ^ 2 = 0) :
    ∀ ρ : CriticalZeros, ρ ∉ F →
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0 := by
  have hb := (canonical_positive_analysis_finite_tail_bound t ht F x).1
  have hf := (canonical_finite_selected_correction_iff t ht S F δ hδ).mp hF x
  have hz : ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
      (∑ ρ ∈ F, ‖⟪positiveGreenColumn
        (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2) = 0 := by
    linarith
  rw [canonical_positive_analysis_tail_identity t ht F x] at hz
  let p := positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ))
  have hs := (canonical_actor_columns_summable t ht).1
  have hb' (ρ : CriticalZeros) : ‖⟪p ρ, x⟫_ℂ‖ ^ 2 ≤ ‖p ρ‖ ^ 2 * ‖x‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_inner_le_norm (𝕜 := ℂ) (p ρ) x) 2
  have ha : Summable (fun ρ => ‖⟪p ρ, x⟫_ℂ‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb' (hs.mul_right (‖x‖ ^ 2))
  intro ρ hρ
  have h := (ha.comp_injective (Subtype.val_injective : Function.Injective
    (Subtype.val : {ρ : CriticalZeros // ρ ∉ F} → CriticalZeros))).le_tsum ⟨ρ, hρ⟩
    (fun _ _ => sq_nonneg _)
  change ‖⟪p ρ, x⟫_ℂ‖ ^ 2 ≤
    (∑' τ : {τ : CriticalZeros // τ ∉ F}, ‖⟪p τ.1, x⟫_ℂ‖ ^ 2) at h
  change (∑' τ : {τ : CriticalZeros // τ ∉ F}, ‖⟪p τ.1, x⟫_ℂ‖ ^ 2) = 0 at hz
  rw [hz] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (⟪p ρ, x⟫_ℂ)])
