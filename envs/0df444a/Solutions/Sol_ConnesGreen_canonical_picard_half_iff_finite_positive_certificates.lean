-- Prove2me | solution 1 for ConnesGreen.canonical_picard_half_iff_finite_positive_certificates
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T20:32:02.962702+00:00
-- url     : https://prove2.me/submissions/f8053fe4-76a7-46b4-b2c2-279e7fd8b49e

import Theorems.Thm_ConnesGreen_RG0Integration_original_picard_half_iff_covariance
import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

private theorem tail_bound_helper (t : ℝ) (ht : 0 < t)
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

private theorem cutoff_helper (t : ℝ) (ht : 0 < t)
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

private theorem covariance_helper
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

theorem solution
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) ↔
    ∀ δ : ℝ, 0 < δ → ∃ F : Finset CriticalZeros,
      S ⊆ F ∧ (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) < δ ∧
      ∀ x : Physical t, ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 ≤
        (∑ ρ ∈ F, ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2) +
          δ * ‖x‖ ^ 2 := by
  have hquad := (RG0Integration.original_picard_half_iff_covariance t ht S).trans
    (covariance_helper _
      (ContinuousLinearMap.isPositive_self_comp_adjoint (canonicalPositiveSynthesis t ht)).isSelfAdjoint
      (canonicalSelectedSynthesis t ht S))
  have he (x : Physical t) : RCLike.re ⟪canonicalPositiveCovariance t ht x, x⟫_ℂ =
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 := by
    have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left x
    simp only [ContinuousLinearMap.adjoint_adjoint] at hp
    exact hp.symm
  change ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
    ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) ↔
      ∀ x : Physical t, ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 ≤
        RCLike.re ⟪canonicalPositiveCovariance t ht x, x⟫_ℂ at hquad
  simp only [he] at hquad
  rw [hquad]
  constructor
  · intro h δ hδ
    obtain ⟨F, hSF, hclosed, htail⟩ := cutoff_helper t ht S δ hδ
    refine ⟨F, hSF, hclosed, htail, ?_⟩
    intro x
    have hb := (tail_bound_helper t ht F x).2
    have hm := mul_le_mul_of_nonneg_right htail.le (sq_nonneg ‖x‖)
    have hx := h x
    linarith
  · intro h x
    by_contra hn
    have hgap : 0 < ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
        ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 := sub_pos.mpr (lt_of_not_ge hn)
    let δ := (‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2) / (2 * (‖x‖ ^ 2 + 1))
    have hδ : 0 < δ := div_pos hgap (by positivity)
    obtain ⟨F, _, _, _, hF⟩ := h δ hδ
    have hb := (tail_bound_helper t ht F x).1
    have hx := hF x
    have hm : δ * (2 * (‖x‖ ^ 2 + 1)) =
        ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
          ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 := div_mul_cancel₀ _ (by positivity)
    nlinarith [sq_nonneg ‖x‖]
