-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_endpoint_half_iff_original_shell_obligations
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T05:58:28.422338+00:00
-- url     : https://prove2.me/submissions/db467d3d-d91b-4da5-85e1-a023b0f222a0

import Definitions.Def_ConnesGreen_original_quartet
import Theorems.Thm_ConnesGreen_canonical_scaled_covariance_le_iff_shell_conditions
import Theorems.Thm_ConnesGreen_exists_original_window_inclusion
import Theorems.Thm_ConnesGreen_canonical_quartet_last_inner_half_window
import Theorems.Thm_ConnesGreen_positiveSupportRadius_positive
import Theorems.Thm_ConnesGreen_canonicalPicardMarker_lower_iff_all_regularized
import Theorems.Thm_WeilDefect_MarkerStability_marker_lower_iff_scaled_covariance_le
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
import Definitions.Def_WeilMarker_regularized_cost
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
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
private lemma recovered_scalar_identity_mono {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {a b : ℝ} (hab : a ≤ b) :
    a • (1 : K →L[ℂ] K) ≤ b • 1 :=
  smul_le_smul_of_nonneg_right hab zero_le_one

private lemma recovered_scalar_lower_of_norm_close {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (A B : K →L[ℂ] K)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (a η : ℝ)
    (ha : a • (1 : K →L[ℂ] K) ≤ A) (hη : ‖A - B‖ ≤ η) :
    (a - η) • (1 : K →L[ℂ] K) ≤ B := by
  have hd := IsSelfAdjoint.le_algebraMap_norm_self (hA.sub hB)
  have he : A - B ≤ η • (1 : K →L[ℂ] K) := hd.trans (by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_le_smul_of_nonneg_right hη (zero_le_one : (0 : K →L[ℂ] K) ≤ 1))
  rw [sub_smul]
  exact sub_le_iff_le_add.mpr (by
    simpa only [add_comm] using ha.trans (sub_le_iff_le_add.mp he))


private lemma recovered_scalar_lower_iff_positive_approximations {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (A : K →L[ℂ] K) (a : ℝ) :
    a • (1 : K →L[ℂ] K) ≤ A ↔
      ∀ η : ℝ, 0 < η → (a - η) • (1 : K →L[ℂ] K) ≤ A := by
  constructor
  · intro h η hη
    exact (recovered_scalar_identity_mono (K := K) (by linarith : a - η ≤ a)).trans h
  · intro h
    have ht : Tendsto (fun η : ℝ => (a - η) • (1 : K →L[ℂ] K))
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (a • (1 : K →L[ℂ] K))) := by
      simpa using ((tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)).smul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : K →L[ℂ] K))
          (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1)))
    apply isClosed_Iic.mem_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact h η hη

private lemma recovered_canonicalPicardMarker_le_regularized_marker (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (ε : ℝ) (hε : 0 < ε) :
    canonicalPicardMarker t ht S ≤ canonicalRegularizedMarker t ht S ε :=
  (canonicalPicardMarker_spec t ht S).2.2.1.1 (mem_image_of_mem _ hε)

private lemma recovered_canonical_endpoint_lower_iff_local_regularized_bounds (c : ℝ) (hc : 0 ≤ c)
    (S : Finset CriticalZeros) (a : ℝ) :
    a • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
    ∀ η : ℝ, 0 < η → ∃ T : ℝ, ∃ hT : 0 < T, c < T ∧
      ∀ ε : ℝ, 0 < ε → (a - η) • 1 ≤ canonicalRegularizedMarker T hT S ε := by
  constructor
  · intro ha η hη
    have hlim := (canonicalSupportRightMarker_spec c hc S).2.2.2
    have hn : Tendsto (fun T => ‖canonicalSupportRightMarker c hc S -
        positiveWindowPicardMarker T S‖) (nhdsWithin c (Ioi c)) (nhds (0 : ℝ)) := by
      simpa using (((tendsto_const_nhds : Tendsto
        (fun _ : ℝ => canonicalSupportRightMarker c hc S)
        (nhdsWithin c (Ioi c)) (nhds (canonicalSupportRightMarker c hc S))).sub hlim).norm)
    have hev := (tendsto_order.mp hn).2 η hη
    have hev2 : ∀ᶠ T in nhdsWithin c (Ioi c), c < T ∧
        ‖canonicalSupportRightMarker c hc S - positiveWindowPicardMarker T S‖ < η := by
      filter_upwards [self_mem_nhdsWithin, hev] with T hct hn
      exact ⟨hct, hn⟩
    obtain ⟨T, hct, hnorm⟩ := hev2.exists
    have hT : 0 < T := lt_of_le_of_lt hc hct
    rw [positiveWindowPicardMarker_eq T hT S] at hnorm
    have hself : IsSelfAdjoint (canonicalSupportRightMarker c hc S) :=
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
        (canonicalSupportRightMarker_spec c hc S).1).isSelfAdjoint
    have hb := recovered_scalar_lower_of_norm_close _ _ hself
      (canonicalPicardMarker_selfAdjoint T hT S) a η ha hnorm.le
    exact ⟨T, hT, hct, fun ε hε => hb.trans
      (recovered_canonicalPicardMarker_le_regularized_marker T hT S ε hε)⟩
  · intro h
    apply (recovered_scalar_lower_iff_positive_approximations _ a).mpr
    intro η hη
    obtain ⟨T, hT, hct, hb⟩ := h η hη
    have hinner : (a - η) • 1 ≤ canonicalPicardMarker T hT S :=
      (canonicalPicardMarker_spec T hT S).2.2.1.2 (by
        rintro _ ⟨ε, hε, rfl⟩
        exact hb ε hε)
    have houter : canonicalPicardMarker T hT S ≤ canonicalSupportRightMarker c hc S := by
      have hh := (canonicalSupportRightMarker_spec c hc S).2.2.1.1
        (mem_image_of_mem (fun t => positiveWindowPicardMarker t S) hct)
      simpa only [positiveWindowPicardMarker_eq T hT S] using hh
    exact hinner.trans houter

private lemma shell_endpoint_local_covariance (c : ℝ) (hc : 0 ≤ c)
    (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
    ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ T : ℝ, ∃ hT : 0 < T, c < T ∧
      canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint ≤
        ((1 / 2 - η)⁻¹ - 1) • canonicalPositiveCovariance T hT := by
  rw [recovered_canonical_endpoint_lower_iff_local_regularized_bounds]
  constructor
  · intro h η hη hηhalf
    obtain ⟨T, hT, hcT, hb⟩ := h η hη
    refine ⟨T, hT, hcT, ?_⟩
    exact (amr_canonicalPicardMarker_lower_iff_covariance T hT S (1 / 2 - η)
      (by linarith) (by linarith)).mp
      ((canonicalPicardMarker_lower_iff_all_regularized T hT S (1 / 2 - η)).mpr hb)
  · intro h η hη
    let α : ℝ := min (η / 2) (1 / 4)
    have hα : 0 < α := lt_min (by linarith) (by norm_num)
    have hαhalf : α < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
    have hαη : α ≤ η := (min_le_left _ _).trans (by linarith)
    obtain ⟨T, hT, hcT, hb⟩ := h α hα hαhalf
    refine ⟨T, hT, hcT, ?_⟩
    have hi := (amr_canonicalPicardMarker_lower_iff_covariance T hT S (1 / 2 - α)
      (by linarith) (by linarith)).mpr hb
    intro ε hε
    exact (recovered_scalar_identity_mono (K := ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))
      (by linarith : 1 / 2 - η ≤ 1 / 2 - α)).trans
      ((canonicalPicardMarker_lower_iff_all_regularized T hT S (1 / 2 - α)).mp hi ε hε)
private lemma shell_endpoint_original_shell
    (c : ℝ) (hc : 0 < c) (S : Finset CriticalZeros)
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker c hc S) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc.le S ↔
    ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ T : ℝ, ∃ hT : 0 < T, c < T ∧
      ∃ U : Physical c →ₗᵢ[ℂ] Physical T,
        (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
          U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
        let D := ((1 / 2 - η)⁻¹ - 1) • canonicalPositiveCovariance T hT -
          canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint
        (∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
          0 ≤ RCLike.re ⟪D z, z⟫_ℂ) ∧
        (∀ x : Physical c, ∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
          ‖⟪D (U x), z⟫_ℂ‖ ^ 2 ≤ RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ) := by
  rw [shell_endpoint_local_covariance c hc.le S]
  have hk : ∀ η : ℝ, 0 < η → η < 1 / 2 → 1 ≤ ((1 / 2 - η)⁻¹ - 1) := by
    intro η hη hηhalf
    have hi := one_div_lt_one_div_of_lt (by linarith : 0 < (1 / 2 : ℝ) - η)
      (by linarith : (1 / 2 : ℝ) - η < 1 / 2)
    norm_num at hi
    linarith
  constructor
  · intro h η hη hηhalf
    obtain ⟨T, hT, hcT, hb⟩ := h η hη hηhalf
    obtain ⟨U, hU⟩ := exists_original_window_inclusion c T hc hT hcT.le
    exact ⟨T, hT, hcT, U, hU,
      (canonical_scaled_covariance_le_iff_shell_conditions c T hc hT hcT.le S U hU hhalf
        _ (hk η hη hηhalf)).mp hb⟩
  · intro h η hη hηhalf
    obtain ⟨T, hT, hcT, U, hU, hb⟩ := h η hη hηhalf
    exact ⟨T, hT, hcT,
      (canonical_scaled_covariance_le_iff_shell_conditions c T hc hT hcT.le S U hU hhalf
        _ (hk η hη hηhalf)).mpr hb⟩

theorem solution
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
      ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ (quartet ρ)}, ℂ) →L[ℂ]
      ℓ²({τ : CriticalZeros // τ ∈ (quartet ρ)}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ) ↔
    ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ T : ℝ, ∃ hT : 0 < T, c < T ∧
      ∃ U : Physical c →ₗᵢ[ℂ] Physical T,
        (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
          U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
        let D := ((1 / 2 - η)⁻¹ - 1) • canonicalPositiveCovariance T hT -
          canonicalSelectedSynthesis T hT (quartet ρ) ∘L (canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
        (∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
          0 ≤ RCLike.re ⟪D z, z⟫_ℂ) ∧
        (∀ x : Physical c, ∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
          ‖⟪D (U x), z⟫_ℂ‖ ^ 2 ≤ RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ)) := by
  obtain ⟨c, hrc, hcut⟩ := canonical_quartet_last_inner_half_window ρ hoff
  have hc : 0 < c := positiveSupportRadius_positive.trans_le hrc
  exact ⟨c, hc, hrc, hcut,
    shell_endpoint_original_shell c hc (quartet ρ)
      ((hcut c hc).mpr le_rfl)⟩
