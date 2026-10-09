-- Prove2me | solution 1 for ConnesGreen.canonical_positive_threshold_orthogonal_gap
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T06:30:20.716038+00:00
-- url     : https://prove2.me/submissions/6eca96bb-7126-4374-9269-10e21e22816f

import Definitions.Def_ConnesGreen_positive_endpoint_support
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

import Theorems.Thm_ConnesGreen_canonicalPositiveCovariance_compact
import Theorems.Thm_ConnesGreen_canonical_selected_form_ge_overlap_shift
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative ContinuousFunctionalCalculus WeilDefect.MarkerStability
namespace ConnesGreen
private theorem finite_coefficients (F : Finset CriticalZeros) :
    FiniteDimensional ℂ (ℓ²({ρ : CriticalZeros // ρ ∈ F}, ℂ)) := by
  let L : ℓ²({ρ : CriticalZeros // ρ ∈ F}, ℂ) →ₗ[ℂ]
      ({ρ : CriticalZeros // ρ ∈ F} → ℂ) :=
    { toFun := fun f ρ => f ρ
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply FiniteDimensional.of_injective L
  intro f g h
  apply lp.ext
  exact h
theorem canonicalLossCovariance_compact (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) : IsCompactOperator (canonicalLossCovariance t ht S) := by
  letI : FiniteDimensional ℂ (ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) := finite_coefficients S
  exact ((isCompactOperator_of_locallyCompactSpace_rng
    (canonicalSelectedSynthesis t ht S)).comp_clm
      (canonicalSelectedSynthesis t ht S).adjoint).sub
    (canonicalPositiveCovariance_compact t ht)
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
theorem canonicalLossCovariance_selfAdjoint (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) : IsSelfAdjoint (canonicalLossCovariance t ht S) := by
  exact (ContinuousLinearMap.isPositive_self_comp_adjoint
    (canonicalSelectedSynthesis t ht S)).isSelfAdjoint.sub
    (ContinuousLinearMap.isPositive_self_comp_adjoint
      (canonicalPositiveSynthesis t ht)).isSelfAdjoint
private instance hilbertRealCFC (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    IsometricContinuousFunctionalCalculus ℝ (H →L[ℂ] H) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := H →L[ℂ] H)
private theorem compact_positive_endpoint_gap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hcompact : IsCompactOperator A)
    (μ : ℝ) (hμ : 0 < μ)
    (hupper : ∀ x : H, RCLike.re ⟪A x, x⟫_ℂ ≤ μ * ‖x‖ ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : H,
      x ∈ (Module.End.eigenspace A.toLinearMap (μ : ℂ))ᗮ →
      c * ‖x‖ ^ 2 ≤ μ * ‖x‖ ^ 2 - RCLike.re ⟪A x, x⟫_ℂ := by
  let E := Module.End.eigenspace A.toLinearMap (μ : ℂ)
  have hinv : ∀ x ∈ Eᗮ, A x ∈ Eᗮ := by
    intro x hx
    apply (E.mem_orthogonal _).mpr
    intro z hz
    change ⟪z, A.toLinearMap x⟫_ℂ = 0
    rw [← hA.isSymmetric z x]
    rw [Module.End.mem_eigenspace_iff.mp hz, inner_smul_left,
      (E.mem_orthogonal x).mp hx z hz, mul_zero]
  let B : Eᗮ →L[ℂ] Eᗮ := A.restrict hinv
  have hB : IsSelfAdjoint B := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    exact hA.isSymmetric (x : H) (y : H)
  have hBc : IsCompactOperator B := hcompact.restrict' hinv
  have hnot : μ ∉ spectrum ℝ B := by
    intro hm
    have hmC := spectrum.algebraMap_mem ℂ hm
    simp only [RCLike.algebraMap_eq_ofReal] at hmC
    change (μ : ℂ) ∈ spectrum ℂ B at hmC
    have hv := (hBc.hasEigenvalue_iff_mem_spectrum (Complex.ofReal_ne_zero.mpr hμ.ne')).mpr hmC
    obtain ⟨x, hx, hxn⟩ := hv.exists_hasEigenvector
    have he : B x = (μ : ℂ) • x := Module.End.mem_genEigenspace_one.mp hx
    have hxE : (x : H) ∈ E := by
      apply Module.End.mem_eigenspace_iff.mpr
      exact congrArg Subtype.val he
    have hz : (x : H) = 0 := Submodule.disjoint_def.mp E.orthogonal_disjoint _ hxE x.2
    exact hxn (Subtype.ext hz)
  rcases subsingleton_or_nontrivial Eᗮ with htr | htr
  · letI := htr
    refine ⟨μ, hμ, ?_⟩
    intro x hx
    have hz : x = 0 := congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : Eᗮ) 0)
    simp [hz]
  · letI := htr
    letI : ContinuousFunctionalCalculus ℝ (Eᗮ →L[ℂ] Eᗮ) IsSelfAdjoint :=
      (hilbertRealCFC Eᗮ).toContinuousFunctionalCalculus
    obtain ⟨m, hm, hmax⟩ := (isCompact_spectrum (R := ℝ) (p := IsSelfAdjoint) B).exists_isMaxOn
      ((hilbertRealCFC Eᗮ).toContinuousFunctionalCalculus.spectrum_nonempty B hB)
      (show ContinuousOn (fun r : ℝ => r) (spectrum ℝ B) from continuous_id.continuousOn)
    have scalar_sa (a : ℝ) : IsSelfAdjoint (a • (1 : Eᗮ →L[ℂ] Eᗮ)) := by
      change IsSelfAdjoint ((a : ℂ) • (1 : Eᗮ →L[ℂ] Eᗮ))
      apply IsSelfAdjoint.smul
      · change (starRingEnd ℂ) (a : ℂ) = (a : ℂ)
        simp
      · exact ContinuousLinearMap.isPositive_one.isSelfAdjoint
    have scalar_quad (a : ℝ) (x : Eᗮ) :
        RCLike.re ⟪(a • (1 : Eᗮ →L[ℂ] Eᗮ)) x, x⟫_ℂ = a * ‖x‖ ^ 2 := by
      change RCLike.re ⟪(a : ℂ) • x, x⟫_ℂ = _
      rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow, ← Complex.ofReal_mul]
    have hBupper : B ≤ algebraMap ℝ (Eᗮ →L[ℂ] Eᗮ) μ := by
      rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.le_def,
        ContinuousLinearMap.isPositive_def']
      refine ⟨?_, ?_⟩
      · exact IsSelfAdjoint.sub (R := Eᗮ →L[ℂ] Eᗮ) (scalar_sa μ) hB
      · intro x
        change 0 ≤ RCLike.re ⟪(μ • (1 : Eᗮ →L[ℂ] Eᗮ) - B) x, x⟫_ℂ
        rw [sub_apply, inner_sub_left, map_sub, scalar_quad]
        exact sub_nonneg.mpr (hupper (x : H))
    have hmle := (le_algebraMap_iff_spectrum_le hB).mp hBupper m hm
    have hmlt : m < μ := lt_of_le_of_ne hmle (by intro he; exact hnot (he ▸ hm))
    have hb : max m 0 < μ := max_lt hmlt hμ
    have hbound : B ≤ algebraMap ℝ (Eᗮ →L[ℂ] Eᗮ) (max m 0) :=
      le_algebraMap_of_spectrum_le (fun r hr => (hmax hr).trans (le_max_left m 0)) hB
    refine ⟨μ - max m 0, sub_pos.mpr hb, ?_⟩
    intro x hx
    let y : Eᗮ := ⟨x, hx⟩
    rw [ContinuousLinearMap.le_def] at hbound
    have hp := hbound.re_inner_nonneg_left y
    rw [Algebra.algebraMap_eq_smul_one, sub_apply, inner_sub_left, map_sub, scalar_quad] at hp
    change 0 ≤ max m 0 * ‖x‖ ^ 2 - RCLike.re ⟪A x, x⟫_ℂ at hp
    nlinarith
end ConnesGreen
theorem solution (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (hμ : 0 < canonicalCertificateThreshold t ht S) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Physical t,
      x ∈ (canonicalMaximizingSpace t ht S)ᗮ →
      c * ‖x‖ ^ 2 ≤ canonicalSharpMargin t ht S x := by
  obtain ⟨c, hc, hb⟩ := compact_positive_endpoint_gap
    (canonicalLossCovariance t ht S) (canonicalLossCovariance_selfAdjoint t ht S)
    (canonicalLossCovariance_compact t ht S) _ hμ (fun x => by
      rw [canonicalLossCovariance_quadratic]
      have h := canonical_selected_form_ge_sharp_threshold t ht S x
      linarith)
  refine ⟨c, hc, ?_⟩
  intro x hx
  have h := hb x hx
  rw [canonicalLossCovariance_quadratic] at h
  unfold canonicalSharpMargin
  linarith
