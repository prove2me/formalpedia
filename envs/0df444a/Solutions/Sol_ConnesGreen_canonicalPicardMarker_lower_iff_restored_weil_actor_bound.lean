-- Prove2me | solution 1 for ConnesGreen.canonicalPicardMarker_lower_iff_restored_weil_actor_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T03:03:06.587651+00:00
-- url     : https://prove2.me/submissions/7da7e102-9ed2-4408-9ad8-0e30f13c7374

import Theorems.Thm_WeilDefect_MarkerStability_marker_lower_iff_scaled_covariance_le
import Theorems.Thm_ConnesGreen_canonicalPicardMarker_lower_iff_all_regularized
import Theorems.Thm_ConnesGreen_covariance_le_iff_original_tests
import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
private lemma amr_scaled_covariance_le_iff_all_regularized {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A B : H →L[ℂ] H)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    B ≤ κ • A ↔ ∀ ε : ℝ, 0 < ε → B ≤ κ • (A + ε • 1) := by
  constructor
  · intro h ε hε
    exact h.trans (smul_le_smul_of_nonneg_left
      (le_add_of_nonneg_right (smul_nonneg hε.le (zero_le_one : (0 : H →L[ℂ] H) ≤ 1))) hκ)
  · intro h
    have hi : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have ht : Tendsto (fun ε : ℝ => κ • (A + ε • (1 : H →L[ℂ] H)))
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (κ • A)) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => A)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds A)).add
        (hi.smul_const (1 : H →L[ℂ] H))).const_smul κ
    apply isClosed_Ici.mem_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact h ε hε

private lemma amr_nonnegative_smul_selfAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H) (hA : 0 ≤ A)
    (κ : ℝ) (hκ : 0 ≤ κ) : IsSelfAdjoint (κ • A) :=
  ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (smul_nonneg hκ hA)).isSelfAdjoint

private theorem amr_partition_helper (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (h : Physical t) :
    ‖(ContinuousLinearMap.adjoint (canonicalSelectedSynthesis t ht S)) h‖ ^ 2 +
      ‖(ContinuousLinearMap.adjoint (canonicalBackgroundSynthesis t ht S)) h‖ ^ 2 =
      ‖(ContinuousLinearMap.adjoint (canonicalNegativeSynthesis t ht)) h‖ ^ 2 := by
  rw [canonicalSelectedSynthesis, canonicalBackgroundSynthesis, canonicalNegativeSynthesis,
    columnSynthesis_adjoint_norm_sq, columnSynthesis_adjoint_norm_sq,
    columnSynthesis_adjoint_norm_sq]
  have hs : Summable (fun ρ : CriticalZeros =>
      ‖⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, h⟫_ℂ‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun ρ => ?_) ((canonical_actor_columns_summable t ht).2.mul_right (‖h‖ ^ 2))
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_inner_le_norm (𝕜 := ℂ)
          (negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) h) 2
  exact hs.tsum_subtype_add_tsum_subtype_compl (S : Set CriticalZeros)

private lemma amr_regularized_covariance_strictPositive
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : K →L[ℂ] H) (ε : ℝ) (hε : 0 < ε) :
    IsStrictlyPositive (P ∘L P.adjoint + ε • 1) := by
  exact IsStrictlyPositive.nonneg_add
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_self_comp_adjoint P))
    ((isStrictlyPositive_one (A := H →L[ℂ] H)).smul hε)
private lemma amr_canonical_regularized_covariance_strictPositive (t : ℝ) (ht : 0 < t)
    (ε : ℝ) (hε : 0 < ε) : IsStrictlyPositive (canonicalPositiveCovariance t ht + ε • 1) := by
  exact amr_regularized_covariance_strictPositive (canonicalPositiveSynthesis t ht) ε hε
private lemma amr_canonicalPicardMarker_lower_iff_covariance
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    β • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S ↔
    canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint ≤
      (β⁻¹ - 1) • canonicalPositiveCovariance t ht := by
  have hκ : 0 ≤ β⁻¹ - 1 := by
    have hi : 1 < β⁻¹ := (one_lt_inv₀ hβ).mpr hβ1
    linarith
  rw [canonicalPicardMarker_lower_iff_all_regularized,
    amr_scaled_covariance_le_iff_all_regularized _ _ (β⁻¹ - 1) hκ]
  apply forall_congr'
  intro ε
  apply imp_congr_right
  intro hε
  exact marker_lower_iff_scaled_covariance_le _
    (amr_canonical_regularized_covariance_strictPositive t ht ε hε) _ β hβ hβ1
private lemma amr_canonical_positive_covariance_arithmetic_energy
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    RCLike.re ⟪canonicalPositiveCovariance t ht (sourceEmbed t (problemOneL g)),
      sourceEmbed t (problemOneL g)⟫_ℂ =
      (weilDistribution (conv g (starInv g))).re +
        ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
        ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 := by
  let x := sourceEmbed t (problemOneL g)
  have he := canonical_signed_actor_arithmetic t ht g hg
  have hpart := amr_partition_helper t ht S x
  have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint] at hp
  change RCLike.re ⟪(canonicalPositiveSynthesis t ht ∘L (canonicalPositiveSynthesis t ht).adjoint) x, x⟫_ℂ = _
  rw [← hp]
  dsimp [x] at *
  linarith
theorem solution
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    β • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S ↔
    ∀ g : ℝ → ℂ, SupportedTest t g →
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
      (β⁻¹ - 1) * ((weilDistribution (conv g (starInv g))).re +
        ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
        ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2) := by
  rw [amr_canonicalPicardMarker_lower_iff_covariance t ht S β hβ hβ1]
  have hκ : 0 ≤ β⁻¹ - 1 := by
    have hi : 1 < β⁻¹ := (one_lt_inv₀ hβ).mpr hβ1
    linarith
  have hpos : 0 ≤ canonicalPositiveCovariance t ht :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_self_comp_adjoint _)
  rw [covariance_le_iff_original_tests t ht _
    (amr_nonnegative_smul_selfAdjoint _ hpos (β⁻¹ - 1) hκ) _]
  apply forall_congr'
  intro g
  apply imp_congr_right
  intro hg
  have hr : RCLike.re ⟪((β⁻¹ - 1) • canonicalPositiveCovariance t ht)
      (sourceEmbed t (problemOneL g)), sourceEmbed t (problemOneL g)⟫_ℂ =
      (β⁻¹ - 1) * RCLike.re ⟪canonicalPositiveCovariance t ht
        (sourceEmbed t (problemOneL g)), sourceEmbed t (problemOneL g)⟫_ℂ := by
    letI := InnerProductSpace.rclikeToReal ℂ (Physical t)
    simp only [← real_inner_eq_re_inner ℂ, ContinuousLinearMap.smul_apply, real_inner_smul_left]
  rw [hr, amr_canonical_positive_covariance_arithmetic_energy t ht S g hg]
