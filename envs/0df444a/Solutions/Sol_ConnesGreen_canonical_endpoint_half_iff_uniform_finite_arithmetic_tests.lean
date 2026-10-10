-- Prove2me | solution 1 for ConnesGreen.canonical_endpoint_half_iff_uniform_finite_arithmetic_tests
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T02:12:59.671478+00:00
-- url     : https://prove2.me/submissions/d4bc826f-3899-43bc-814c-43426a9edd48

import Theorems.Thm_ConnesGreen_canonicalRegularizedMarker_window_antitone
import Theorems.Thm_ConnesGreen_actual_zero_uniform_marker_recovery
import Theorems.Thm_WeilDefect_MarkerStability_tail_marker_stability
import Theorems.Thm_ConnesGreen_canonical_finite_marker_lower_iff_arithmetic_tests
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
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

private def recovered_canonicalFiniteRestoredMarker (t : ℝ) (ht : 0 < t)
    (S F : Finset CriticalZeros) (ε : ℝ) :=
  marker (canonicalPositiveCovariance t ht + ε • 1 - canonicalTailCovariance t ht F)
    (canonicalSelectedSynthesis t ht S)

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

/-- Exact neighborhood version of the remaining estimate: the nearby support
interval may depend on accuracy, while every positive regularization is kept. -/
private lemma recovered_canonical_endpoint_lower_iff_uniform_window_bounds (c : ℝ) (hc : 0 ≤ c)
    (S : Finset CriticalZeros) (a : ℝ) :
    a • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + δ →
        ∀ ε : ℝ, 0 < ε → (a - η) • 1 ≤ canonicalRegularizedMarker T hT S ε := by
  rw [recovered_canonical_endpoint_lower_iff_local_regularized_bounds]
  constructor
  · intro h η hη
    obtain ⟨T, hT, hct, hb⟩ := h η hη
    refine ⟨T - c, by linarith, ?_⟩
    intro U hU hcU hUT ε hε
    exact (hb ε hε).trans
      (canonicalRegularizedMarker_window_antitone U T hU hT (by linarith) S ε hε)
  · intro h η hη
    obtain ⟨δ, hδ, hb⟩ := h η hη
    have hT : 0 < c + δ / 2 := by linarith
    refine ⟨c + δ / 2, hT, by linarith, ?_⟩
    exact hb (c + δ / 2) hT (by linarith) (by linarith)

private lemma recovered_canonical_uniform_diagonal_marker_recovery (T : ℝ) (S : Finset CriticalZeros)
    (ε α : ℝ) (hε : 0 < ε) (hα : 0 < α) (hα1 : α < 1) :
    ∃ F : Finset CriticalZeros, S ⊆ F ∧
      (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ‖canonicalTailCovariance t ht F‖ ≤ α * ε ∧
        IsStrictlyPositive (canonicalPositiveCovariance t ht + ε • 1 - canonicalTailCovariance t ht F) ∧
        0 ≤ canonicalRegularizedMarker t ht S ε - recovered_canonicalFiniteRestoredMarker t ht S F ε ∧
        ‖canonicalRegularizedMarker t ht S ε - recovered_canonicalFiniteRestoredMarker t ht S F ε‖ ≤ α := by
  obtain ⟨F, hinc, hclosed, hrec⟩ := actual_zero_uniform_marker_recovery T S ε α hε hα hα1
  refine ⟨F, hinc, hclosed, ?_⟩
  intro t ht htT
  obtain ⟨P, M, B, hP, hM, hB, htail, hpos, hdiff, hnorm⟩ := hrec t ht htT
  have hp := canonicalPositiveSynthesis_unique t ht P hP
  have hm := canonicalSelectedSynthesis_unique t ht S M hM
  have hb := canonicalBackgroundSynthesis_unique t ht F B hB
  subst P; subst M; subst B
  exact ⟨htail, hpos, hdiff, hnorm⟩

private lemma recovered_canonical_marker_tail_stability (t : ℝ) (ht : 0 < t)
    (S F : Finset CriticalZeros) (ε α : ℝ)
    (hε : 0 < ε) (hα : 0 ≤ α) (hα1 : α < 1)
    (htail : ‖canonicalTailCovariance t ht F‖ ≤ α * ε) :
    IsStrictlyPositive (canonicalPositiveCovariance t ht + ε • 1 - canonicalTailCovariance t ht F) ∧
      0 ≤ canonicalRegularizedMarker t ht S ε - recovered_canonicalFiniteRestoredMarker t ht S F ε ∧
      ‖canonicalRegularizedMarker t ht S ε - recovered_canonicalFiniteRestoredMarker t ht S F ε‖ ≤ α := by
  apply tail_marker_stability
    (canonicalPositiveCovariance t ht) (canonicalTailCovariance t ht F)
    (canonicalSelectedSynthesis t ht S) _ _ ε α hε hα hα1 htail
  · exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_self_comp_adjoint _)
  · exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_self_comp_adjoint _)

private lemma recovered_canonical_endpoint_lower_iff_uniform_finite_restoration (c : ℝ) (hc : 0 ≤ c)
    (S : Finset CriticalZeros) (a : ℝ) :
    a • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
    ∀ η : ℝ, 0 < η → η < 1 → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ∃ F : Finset CriticalZeros, S ⊆ F ∧
        (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
        ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + δ →
          ‖canonicalTailCovariance T hT F‖ ≤ (η / 2) * ε ∧
          IsStrictlyPositive (canonicalPositiveCovariance T hT + ε • 1 -
            canonicalTailCovariance T hT F) ∧
          (a - η) • 1 ≤ recovered_canonicalFiniteRestoredMarker T hT S F ε := by
  constructor
  · intro ha η hη hη1
    obtain ⟨δ, hδ, hb⟩ :=
      (recovered_canonical_endpoint_lower_iff_uniform_window_bounds c hc S a).mp ha (η / 2)
        (by linarith)
    refine ⟨δ, hδ, ?_⟩
    intro ε hε
    obtain ⟨F, hinc, hclosed, hrec⟩ :=
      recovered_canonical_uniform_diagonal_marker_recovery (c + δ) S ε (η / 2) hε
        (by linarith) (by linarith)
    refine ⟨F, hinc, hclosed, ?_⟩
    intro T hT hct hTδ
    obtain ⟨htail, hpos, hdiff, hnorm⟩ := hrec T hT hTδ.le
    have hd := (CStarAlgebra.norm_le_iff_le_algebraMap _
      (by linarith : 0 ≤ η / 2) hdiff).mp hnorm
    rw [Algebra.algebraMap_eq_smul_one] at hd
    have hbound := hb T hT hct hTδ ε hε
    have hh : (a - η / 2) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) - (η / 2) • 1 ≤
        recovered_canonicalFiniteRestoredMarker T hT S F ε :=
      sub_le_iff_le_add.mpr (by
        simpa only [add_comm] using hbound.trans (sub_le_iff_le_add.mp hd))
    refine ⟨htail, hpos, ?_⟩
    have hs : (a - η) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) =
        (a - η / 2) • 1 - (η / 2) • 1 := by
      calc
        _ = ((a - η / 2) - η / 2) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) := by congr 1; ring
        _ = _ := sub_smul (a - η / 2) (η / 2) (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))
    rw [hs]
    exact hh
  · intro h
    apply (recovered_canonical_endpoint_lower_iff_uniform_window_bounds c hc S a).mpr
    intro η hη
    let α : ℝ := min (η / 2) (1 / 2)
    have hα : 0 < α := lt_min (by linarith) (by norm_num)
    have hα1 : α < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hαη : α ≤ η := (min_le_left _ _).trans (by linarith)
    obtain ⟨δ, hδ, hb⟩ := h α hα hα1
    refine ⟨δ, hδ, ?_⟩
    intro T hT hct hTδ ε hε
    obtain ⟨F, _, _, hrec⟩ := hb ε hε
    obtain ⟨htail, _, hbound⟩ := hrec T hT hct hTδ
    have hdiff := (recovered_canonical_marker_tail_stability T hT S F ε (α / 2) hε
      (by linarith) (by linarith) htail).2.1
    exact (recovered_scalar_identity_mono (K := ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))
      (by linarith : a - η ≤ a - α)).trans (hbound.trans (sub_nonneg.mp hdiff))

theorem solution
    (c : ℝ) (hc : 0 ≤ c) (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
    ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ∃ F : Finset CriticalZeros, S ⊆ F ∧
        (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
        ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + δ →
          ‖canonicalTailCovariance T hT F‖ ≤ (η / 2) * ε ∧
          IsStrictlyPositive (canonicalPositiveCovariance T hT + ε • 1 -
            canonicalTailCovariance T hT F) ∧
          ∀ g : ℝ → ℂ, SupportedTest T g →
            ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 ≤
            ((1 / 2 - η)⁻¹ - 1) * ((weilDistribution (conv g (starInv g))).re +
              ‖(canonicalSelectedSynthesis T hT F).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 +
              ε * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) + (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))) := by
  rw [recovered_canonical_endpoint_lower_iff_uniform_finite_restoration]
  constructor
  · intro h η hη hηhalf
    obtain ⟨δ, hδ, hb⟩ := h η hη (by linarith)
    refine ⟨δ, hδ, ?_⟩
    intro ε hε
    obtain ⟨F, hinc, hclosed, hF⟩ := hb ε hε
    refine ⟨F, hinc, hclosed, ?_⟩
    intro T hT hct hTδ
    obtain ⟨htail, hpos, hbound⟩ := hF T hT hct hTδ
    exact ⟨htail, hpos, (canonical_finite_marker_lower_iff_arithmetic_tests T hT S F ε
      (1 / 2 - η) (by linarith) (by linarith) hpos).mp hbound⟩
  · intro h η hη hη1
    let α : ℝ := min (η / 2) (1 / 4)
    have hα : 0 < α := lt_min (by linarith) (by norm_num)
    have hαhalf : α < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
    have hαη : α ≤ η := (min_le_left _ _).trans (by linarith)
    obtain ⟨δ, hδ, hb⟩ := h α hα hαhalf
    refine ⟨δ, hδ, ?_⟩
    intro ε hε
    obtain ⟨F, hinc, hclosed, hF⟩ := hb ε hε
    refine ⟨F, hinc, hclosed, ?_⟩
    intro T hT hct hTδ
    obtain ⟨htail, hpos, htests⟩ := hF T hT hct hTδ
    have hm := (canonical_finite_marker_lower_iff_arithmetic_tests T hT S F ε
      (1 / 2 - α) (by linarith) (by linarith) hpos).mpr htests
    refine ⟨htail.trans (mul_le_mul_of_nonneg_right (by linarith) hε.le), hpos, ?_⟩
    exact (recovered_scalar_identity_mono (K := ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))
      (by linarith : 1 / 2 - η ≤ 1 / 2 - α)).trans hm

