-- Prove2me | solution 1 for ConnesGreen.RG0Integration.uniform_original_pair_actor_tail
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T23:07:06.619446+00:00
-- url     : https://prove2.me/submissions/327a3236-7351-4801-a6c4-83c90e8411f0

import Theorems.Thm_ConnesGreen_RG0Integration_window_inclusion_original_source_adjoint
import Theorems.Thm_ConnesGreen_exists_original_window_inclusion
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative ContinuousLinearMap Filter Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace ConnesGreen.RG0Integration

private theorem pair_column_mono (t T : ℝ) (ht : 0 < t) (hT : 0 < T) (htT : t ≤ T)
    (ρ : CriticalZeros) :
    ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ‖ ^ 2 +
      ‖negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ‖ ^ 2 ≤
    ‖positiveGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ‖ ^ 2 +
      ‖negativeGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ‖ ^ 2 := by
  obtain ⟨U, hU⟩ := exists_original_window_inclusion t T ht hT htT
  have hs := window_inclusion_original_source_adjoint t T ht hT htT U hU
  have hp : U.toContinuousLinearMap.adjoint
      (positiveGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ) =
      positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ := by
    simp [positiveGreenColumn, weightedGreenColumn, hs] <;> rfl
  have hn : U.toContinuousLinearMap.adjoint
      (negativeGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ) =
      negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ := by
    simp [negativeGreenColumn, weightedGreenColumn, hs] <;> rfl
  have hb : ∀ x : Physical T, ‖U.toContinuousLinearMap.adjoint x‖ ≤ ‖x‖ := by
    intro x
    have h := U.toContinuousLinearMap.adjoint.le_opNorm x
    rw [ContinuousLinearMap.adjoint.norm_map] at h
    exact h.trans (by simpa using mul_le_mul_of_nonneg_right U.norm_toContinuousLinearMap_le (norm_nonneg x))
  have hb1 := hb (positiveGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ)
  have hb2 := hb (negativeGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ)
  rw [hp] at hb1
  rw [hn] at hb2
  nlinarith [norm_nonneg (positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ),
    norm_nonneg (negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ)]

private theorem uniform_pair_tail (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset CriticalZeros, S ⊆ F ∧
      (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      ∀ t : ℝ, ∀ _ht : 0 < t, t ≤ T →
        (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
          (‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2 +
          ‖negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2)) < η := by
  let q : CriticalZeros → ℝ := fun ρ =>
    ‖positiveGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ‖ ^ 2 +
      ‖negativeGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ‖ ^ 2
  have hs : Summable q := (canonical_actor_columns_summable T hT).1.add
    (canonical_actor_columns_summable T hT).2
  have hev := (tendsto_order.mp (tendsto_tsum_compl_atTop_zero q)).2 η hη
  obtain ⟨F₀, hF₀⟩ := eventually_atTop.mp hev
  let G := F₀ ∪ S
  let F := G ∪ G.image reflectedZero
  have hGF : G ⊆ F := Finset.subset_union_left
  have hSF : S ⊆ F := Finset.subset_union_right.trans hGF
  have hF₀F : F₀ ⊆ F := Finset.subset_union_left.trans hGF
  refine ⟨F, hSF, ?_, ?_⟩
  · intro ρ hρ
    rcases Finset.mem_union.mp hρ with hρ | hρ
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hρ)
    · obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hρ
      rw [reflectedZero_involutive]
      exact Finset.mem_union_left _ hτ
  · intro t ht htT
    have hp := (canonical_actor_columns_summable t ht).1.comp_injective
      (Subtype.val_injective : Function.Injective (Subtype.val : {ρ : CriticalZeros // ρ ∉ F} → CriticalZeros))
    have hn := (canonical_actor_columns_summable t ht).2.comp_injective
      (Subtype.val_injective : Function.Injective (Subtype.val : {ρ : CriticalZeros // ρ ∉ F} → CriticalZeros))
    have he := hs.comp_injective
      (Subtype.val_injective : Function.Injective (Subtype.val : {ρ : CriticalZeros // ρ ∉ F} → CriticalZeros))
    have hsum : Summable (fun ρ : {ρ : CriticalZeros // ρ ∉ F} =>
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2 +
        ‖negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) := hp.add hn
    have hbound : (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        (‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2 +
        ‖negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2)) ≤
        ∑' ρ : {ρ : CriticalZeros // ρ ∉ F}, q ρ.1 :=
      hsum.tsum_le_tsum (fun ρ => pair_column_mono t T ht hT htT ρ.1) he
    exact hbound.trans_lt (hF₀ F hF₀F)


private theorem canonical_tail_covariance_bound (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros) :
    ‖canonicalTailCovariance t ht F‖ ≤
      ∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2 := by
  have hcomp := ContinuousLinearMap.opNorm_comp_le
    (canonicalBackgroundSynthesis t ht F) (canonicalBackgroundSynthesis t ht F).adjoint
  rw [ContinuousLinearMap.adjoint.norm_map, ← pow_two] at hcomp
  exact hcomp.trans (columnSynthesis_norm_sq_le _ _)


end ConnesGreen.RG0Integration
theorem solution (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset CriticalZeros, S ⊆ F ∧
      (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
          (∀ ρ, Ptail (lp.single 2 ρ (1 : ℂ)) =
            positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht F‖ < η := by
  obtain ⟨F, hSF, hclosed, hsmall⟩ := ConnesGreen.RG0Integration.uniform_pair_tail T hT S η hη
  refine ⟨F, hSF, hclosed, ?_⟩
  intro t ht htT
  let p := fun ρ : {ρ : CriticalZeros // ρ ∉ F} =>
    positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1
  have hp := (canonical_actor_columns_summable t ht).1.comp_injective
    (Subtype.val_injective : Function.Injective (Subtype.val : {ρ : CriticalZeros // ρ ∉ F} → CriticalZeros))
  have hn := (canonical_actor_columns_summable t ht).2.comp_injective
    (Subtype.val_injective : Function.Injective (Subtype.val : {ρ : CriticalZeros // ρ ∉ F} → CriticalZeros))
  let Ptail := columnSynthesis p hp
  refine ⟨Ptail, ?_, ?_⟩
  · intro ρ
    convert (columnSynthesis_single p hp ρ (1 : ℂ)).trans (one_smul ℂ _) using 1
    congr 1
    ext τ
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs <;> rfl
  · have hcomp := ContinuousLinearMap.opNorm_comp_le Ptail Ptail.adjoint
    rw [ContinuousLinearMap.adjoint.norm_map, ← pow_two] at hcomp
    have hb := add_le_add (hcomp.trans (columnSynthesis_norm_sq_le p hp))
      (ConnesGreen.RG0Integration.canonical_tail_covariance_bound t ht F)
    have he : (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        (‖p ρ‖ ^ 2 + ‖negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2)) =
        (∑' ρ, ‖p ρ‖ ^ 2) + (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
          ‖negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) := hp.tsum_add hn
    calc
      _ ≤ _ := hb
      _ = ∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
          (‖p ρ‖ ^ 2 + ‖negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) := he.symm
      _ < η := hsmall t ht htT
