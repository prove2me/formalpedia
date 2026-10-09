-- Prove2me | solution 1 for ConnesGreen.canonical_positive_threshold_mem_real_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T05:53:34.478283+00:00
-- url     : https://prove2.me/submissions/ae7df8e7-f9a3-4912-a215-ae9d17efd473

import Definitions.Def_ConnesGreen_selected_loss_covariance
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

import Theorems.Thm_ConnesGreen_canonical_selected_form_ge_overlap_shift
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative
open ContinuousFunctionalCalculus
namespace ConnesGreen
private instance physicalRealCFC (t : ℝ) :
    IsometricContinuousFunctionalCalculus ℝ (Physical t →L[ℂ] Physical t) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := Physical t →L[ℂ] Physical t)
theorem arithmeticOverlapShift_nonnegative (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ arithmeticOverlapShift R := by
  have hs : 0 ≤ Real.sinh R-R := sub_nonneg.mpr (Real.self_le_sinh_iff.mpr hR)
  unfold arithmeticOverlapShift primeOverlapEnergyCost
  apply add_nonneg (add_nonneg (by positivity) (le_min (by positivity) (by positivity)))
  exact Finset.sum_nonneg (fun n hn => by positivity)
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
theorem canonicalLossCovariance_selfAdjoint (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) : IsSelfAdjoint (canonicalLossCovariance t ht S) := by
  exact (ContinuousLinearMap.isPositive_self_comp_adjoint
    (canonicalSelectedSynthesis t ht S)).isSelfAdjoint.sub
    (ContinuousLinearMap.isPositive_self_comp_adjoint
      (canonicalPositiveSynthesis t ht)).isSelfAdjoint
theorem canonicalLossCovariance_quadratic (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t) :
    RCLike.re ⟪canonicalLossCovariance t ht S x, x⟫_ℂ =
      ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
        ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 := by
  have hn := (canonicalSelectedSynthesis t ht S).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply] at hn hp
  simp only [canonicalLossCovariance, canonicalPositiveCovariance,
    ContinuousLinearMap.sub_apply, inner_sub_left, map_sub, ContinuousLinearMap.comp_apply]
  rw [← hn, ← hp]
private theorem real_smul_one_selfAdjoint (t : ℝ) (a : ℝ) :
    IsSelfAdjoint (a • (1 : Physical t →L[ℂ] Physical t)) := by
  change IsSelfAdjoint ((a : ℂ) • (1 : Physical t →L[ℂ] Physical t))
  apply IsSelfAdjoint.smul
  · change (starRingEnd ℂ) (a : ℂ) = (a : ℂ)
    simp
  · exact ContinuousLinearMap.isPositive_one.isSelfAdjoint
private theorem loss_le_scalar_iff (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) (a : ℝ) :
    canonicalLossCovariance t ht S ≤ a • 1 ↔
    ∀ x : Physical t, ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 ≤ a * ‖x‖ ^ 2 := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  have hs : IsSelfAdjoint (a • (1 : Physical t →L[ℂ] Physical t) -
      canonicalLossCovariance t ht S) :=
    by
      apply IsSelfAdjoint.sub (R := Physical t →L[ℂ] Physical t)
      · exact real_smul_one_selfAdjoint t a
      · exact canonicalLossCovariance_selfAdjoint t ht S
  simp only [hs, true_and]
  apply forall_congr'
  intro x
  have he : RCLike.re ⟪(a • (1 : Physical t →L[ℂ] Physical t)) x, x⟫_ℂ = a * ‖x‖ ^ 2 := by
    change RCLike.re ⟪(a : ℂ) • x, x⟫_ℂ = _
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [Complex.star_def, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  change (0 ≤ RCLike.re ⟪(a • (1 : Physical t →L[ℂ] Physical t) -
    canonicalLossCovariance t ht S) x, x⟫_ℂ) ↔ _
  rw [ContinuousLinearMap.sub_apply, inner_sub_left, map_sub, he,
    canonicalLossCovariance_quadratic]
  exact sub_nonneg
theorem canonical_threshold_le_iff_loss_covariance (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (a : ℝ) (ha : 0 ≤ a) :
    canonicalCertificateThreshold t ht S ≤ a ↔ canonicalLossCovariance t ht S ≤ a • 1 := by
  rw [loss_le_scalar_iff]
  constructor
  · intro h x
    have hs := canonical_selected_form_ge_sharp_threshold t ht S x
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg ‖x‖)
    linarith
  · intro h
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    by_cases hx : x = 0
    · simpa [hx] using ha
    · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr (h x)
end ConnesGreen
theorem solution (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (hμ : 0 < canonicalCertificateThreshold t ht S) :
    canonicalCertificateThreshold t ht S ∈ spectrum ℝ (canonicalLossCovariance t ht S) := by
  have hμ' : 0 < sSup (Set.range (fun x : Physical t =>
      (‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
        ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2) / ‖x‖ ^ 2)) := hμ
  obtain ⟨a, ha, hx⟩ := exists_lt_of_lt_csSup
    (Set.range_nonempty (fun x : Physical t =>
      (‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
        ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2) / ‖x‖ ^ 2)) hμ'
  obtain ⟨x, rfl⟩ := ha
  have hxne : x ≠ 0 := by intro hz; simp [hz] at hx
  letI : Nontrivial (Physical t) := ⟨⟨x, 0, hxne⟩⟩
  letI : ContinuousFunctionalCalculus ℝ (Physical t →L[ℂ] Physical t) IsSelfAdjoint :=
    (physicalRealCFC t).toContinuousFunctionalCalculus
  let A := canonicalLossCovariance t ht S
  have hs : IsSelfAdjoint A := canonicalLossCovariance_selfAdjoint t ht S
  obtain ⟨m, hm, hmax⟩ := (isCompact_spectrum (R := ℝ) (p := IsSelfAdjoint) A).exists_isMaxOn
    ((physicalRealCFC t).toContinuousFunctionalCalculus.spectrum_nonempty A hs)
    (show ContinuousOn (fun r : ℝ => r) (spectrum ℝ A) from continuous_id.continuousOn)
  have hupper : A ≤ algebraMap ℝ (Physical t →L[ℂ] Physical t)
      (canonicalCertificateThreshold t ht S) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (canonical_threshold_le_iff_loss_covariance t ht S _ hμ.le).mp le_rfl
  have hmle := (le_algebraMap_iff_spectrum_le hs).mp hupper m hm
  have ha : A ≤ algebraMap ℝ (Physical t →L[ℂ] Physical t) (max m 0) :=
    le_algebraMap_of_spectrum_le (fun r hr => (hmax hr).trans (le_max_left m 0)) hs
  have hμle : canonicalCertificateThreshold t ht S ≤ max m 0 :=
    (canonical_threshold_le_iff_loss_covariance t ht S _ (le_max_right m 0)).mpr
      (by simpa only [Algebra.algebraMap_eq_smul_one] using ha)
  have hmpos : 0 < m := by
    by_contra hn
    rw [max_eq_right (le_of_not_gt hn)] at hμle
    linarith
  rw [max_eq_left hmpos.le] at hμle
  have he : m = canonicalCertificateThreshold t ht S := le_antisymm hmle hμle
  simpa [A, he] using hm
