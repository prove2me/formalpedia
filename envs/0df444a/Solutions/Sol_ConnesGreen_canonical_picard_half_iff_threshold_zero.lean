-- Prove2me | solution 1 for ConnesGreen.canonical_picard_half_iff_threshold_zero
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T04:21:01.17365+00:00
-- url     : https://prove2.me/submissions/d031a448-ccce-49eb-9563-e4994d9ada8e

import Definitions.Def_ConnesGreen_sharp_certificate_threshold
import Theorems.Thm_ConnesGreen_canonical_selected_form_ge_overlap_shift
import Theorems.Thm_WeilDefect_MarkerStability_regularized_covariance_le_iff_selected_correction
import Theorems.Thm_ConnesGreen_canonical_finite_certificate_above_sharp_threshold
import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_unrestricted_finite_certificates
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
theorem arithmeticOverlapShift_nonnegative (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ arithmeticOverlapShift R := by
  have hs : 0 ≤ Real.sinh R-R := sub_nonneg.mpr (Real.self_le_sinh_iff.mpr hR)
  unfold arithmeticOverlapShift primeOverlapEnergyCost
  apply add_nonneg (add_nonneg (by positivity) (le_min (by positivity) (by positivity)))
  exact Finset.sum_nonneg (fun n hn => by positivity)
end ConnesGreen
namespace ConnesGreen
private theorem score_le_of_bound (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ x : Physical t, -a * ‖x‖ ^ 2 ≤
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
        ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2) (x : Physical t) :
    (‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2) / ‖x‖ ^ 2 ≤ a := by
  by_cases hx : x = 0
  · simpa [hx] using ha
  · apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr
    have hb := h x
    linarith
private theorem scores_bdd (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    BddAbove (Set.range (fun x : Physical t =>
      (‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
        ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2) / ‖x‖ ^ 2)) := by
  refine ⟨arithmeticOverlapShift t, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact score_le_of_bound t ht S _ (arithmeticOverlapShift_nonnegative t ht.le)
    (fun x => by simpa only using
      canonical_selected_form_ge_overlap_shift t t ht le_rfl S x) x
theorem canonicalCertificateThreshold_nonnegative (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) : 0 ≤ canonicalCertificateThreshold t ht S := by
  apply le_csSup (scores_bdd t ht S)
  exact ⟨0, by simp⟩
theorem canonicalCertificateThreshold_le_overlap_shift (R t : ℝ) (ht : 0 < t)
    (htR : t ≤ R) (S : Finset CriticalZeros) :
    canonicalCertificateThreshold t ht S ≤ arithmeticOverlapShift R := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact score_le_of_bound t ht S _
    (arithmeticOverlapShift_nonnegative R (ht.le.trans htR))
    (fun x => by simpa only using
      canonical_selected_form_ge_overlap_shift R t ht htR S x) x
theorem canonical_selected_form_ge_sharp_threshold (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t) :
    -canonicalCertificateThreshold t ht S * ‖x‖ ^ 2 ≤
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
        ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  · have hs := le_csSup (scores_bdd t ht S) (Set.mem_range_self x)
    have hb := (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mp hs
    change _ ≤ canonicalCertificateThreshold t ht S * ‖x‖ ^ 2 at hb
    linarith
theorem canonicalCertificateThreshold_le_of_finite_certificate
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) (hδ : 0 < δ)
    (hF : 0 ≤ canonicalFiniteSelectedCorrection t ht S F δ) :
    canonicalCertificateThreshold t ht S ≤ δ := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  apply score_le_of_bound t ht S δ hδ.le _ x
  intro y
  have hf := (canonical_finite_selected_correction_iff t ht S F δ hδ).mp hF y
  have hb := (canonical_positive_analysis_finite_tail_bound t ht F y).1
  linarith
end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) ↔
    canonicalCertificateThreshold t ht S = 0 := by
  rw [canonical_picard_half_iff_unrestricted_finite_certificates]
  constructor
  · intro h
    apply le_antisymm _ (canonicalCertificateThreshold_nonnegative t ht S)
    by_contra hn
    have hp : 0 < canonicalCertificateThreshold t ht S := lt_of_not_ge hn
    obtain ⟨F, hF⟩ := h _ (half_pos hp)
    have hb := canonicalCertificateThreshold_le_of_finite_certificate t ht S F _
      (half_pos hp) hF
    linarith
  · intro hz δ hδ
    obtain ⟨F, _, _, _, hF⟩ := canonical_finite_certificate_above_sharp_threshold
      t ht S δ δ (by simpa [hz] using hδ) hδ
    exact ⟨F, hF⟩
