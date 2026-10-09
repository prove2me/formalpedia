-- Prove2me | solution 1 for ConnesGreen.canonical_endpoint_certificate_of_maximizing_capture
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T06:35:20.23345+00:00
-- url     : https://prove2.me/submissions/2f29fe0d-0173-4fdb-bdae-27839e5109f9

import Definitions.Def_ConnesGreen_positive_endpoint_support
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

import Theorems.Thm_ConnesGreen_canonicalPositiveCovariance_compact
import Theorems.Thm_ConnesGreen_canonical_positive_threshold_orthogonal_gap
import Theorems.Thm_WeilDefect_MarkerStability_regularized_covariance_le_iff_selected_correction
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
theorem canonical_positive_threshold_eigenspace_finite (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (hμ : 0 < canonicalCertificateThreshold t ht S) :
    FiniteDimensional ℂ (Module.End.eigenspace (canonicalLossCovariance t ht S).toLinearMap
      (canonicalCertificateThreshold t ht S : ℂ)) := by
  exact ContinuousLinearMap.finite_dimensional_eigenspace (canonicalLossCovariance_compact t ht S) _
    (Complex.ofReal_ne_zero.mpr hμ.ne')
theorem canonical_mem_maximizingSpace_iff (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t) :
    x ∈ canonicalMaximizingSpace t ht S ↔
      canonicalLossCovariance t ht S x = (canonicalCertificateThreshold t ht S : ℂ) • x :=
  Module.End.mem_eigenspace_iff
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
theorem canonical_finite_certificate_iff_tail_margin
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ canonicalFiniteSelectedCorrection t ht S F δ ↔
    ∀ x : Physical t,
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F}, ‖⟪positiveGreenColumn
        (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1, x⟫_ℂ‖ ^ 2) ≤
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
        ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 + δ * ‖x‖ ^ 2 := by
  rw [canonical_finite_selected_correction_iff t ht S F δ hδ]
  apply forall_congr'
  intro x
  rw [← canonical_positive_analysis_tail_identity t ht F x]
  constructor <;> intro h <;> linarith
private theorem canonical_sharp_margin_add_maximizer (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (z y : Physical t)
    (hz : z ∈ canonicalMaximizingSpace t ht S) :
    canonicalSharpMargin t ht S (z + y) = canonicalSharpMargin t ht S y := by
  let μ := canonicalCertificateThreshold t ht S
  let A := canonicalLossCovariance t ht S
  let B : Physical t →L[ℂ] Physical t := μ • 1 - A
  have scalar_sa : IsSelfAdjoint (μ • (1 : Physical t →L[ℂ] Physical t)) := by
    change IsSelfAdjoint ((μ : ℂ) • (1 : Physical t →L[ℂ] Physical t))
    apply IsSelfAdjoint.smul
    · change (starRingEnd ℂ) (μ : ℂ) = (μ : ℂ)
      simp
    · exact ContinuousLinearMap.isPositive_one.isSelfAdjoint
  have hB : IsSelfAdjoint B := IsSelfAdjoint.sub
    (R := Physical t →L[ℂ] Physical t) scalar_sa (canonicalLossCovariance_selfAdjoint t ht S)
  have hBz : B z = 0 := by
    change (μ : ℂ) • z - A z = 0
    rw [(canonical_mem_maximizingSpace_iff t ht S z).mp hz]
    exact sub_self _
  have hcross : ⟪B y, z⟫_ℂ = 0 := by
    apply inner_eq_zero_symm.mp
    change ⟪z, B.toLinearMap y⟫_ℂ = 0
    rw [← hB.isSymmetric z y]
    change ⟪B z, y⟫_ℂ = 0
    rw [hBz, inner_zero_left]
  have hquad (x : Physical t) : RCLike.re ⟪B x, x⟫_ℂ = canonicalSharpMargin t ht S x := by
    have hscalar : RCLike.re ⟪(μ : ℂ) • x, x⟫_ℂ = μ * ‖x‖ ^ 2 := by
      rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow, ← Complex.ofReal_mul]
    change RCLike.re ⟪(μ : ℂ) • x - A x, x⟫_ℂ = _
    rw [inner_sub_left, map_sub, hscalar, canonicalLossCovariance_quadratic]
    unfold canonicalSharpMargin μ
    ring
  rw [← hquad, map_add, hBz, zero_add, inner_add_right, hcross, zero_add, hquad]
end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S F₀ : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S)
    (hcapture : ∀ x : Physical t, x ∈ canonicalMaximizingSpace t ht S →
      ∀ ρ : CriticalZeros, ρ ∉ F₀ →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset CriticalZeros, S ⊆ F ∧ F₀ ⊆ F ∧
      (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) < ε ∧
      0 ≤ canonicalFiniteSelectedCorrection t ht S F (canonicalCertificateThreshold t ht S) := by
  obtain ⟨c, hc, hgap⟩ := canonical_positive_threshold_orthogonal_gap t ht S hμ
  obtain ⟨F, hbase, hreflect, htail⟩ := canonical_positive_tail_cutoff t ht (S ∪ F₀)
    (min ε c) (lt_min hε hc)
  have hSF : S ⊆ F := Finset.Subset.trans Finset.subset_union_left hbase
  have hF₀F : F₀ ⊆ F := Finset.Subset.trans Finset.subset_union_right hbase
  refine ⟨F, hSF, hF₀F, hreflect, htail.trans_le (min_le_left _ _), ?_⟩
  apply (canonical_finite_certificate_iff_tail_margin t ht S F _ hμ).mpr
  intro x
  let E := canonicalMaximizingSpace t ht S
  letI : FiniteDimensional ℂ E := canonical_positive_threshold_eigenspace_finite t ht S hμ
  obtain ⟨z, hz, y, hy, hxy⟩ := Submodule.exists_add_mem_mem_orthogonal (K := E) x
  have hzero (ρ : CriticalZeros) (hρ : ρ ∉ F) :
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, z⟫_ℂ = 0 :=
    hcapture z hz ρ (fun h => hρ (hF₀F h))
  have htailx : (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
      ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1, x⟫_ℂ‖ ^ 2) =
      ∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1, y⟫_ℂ‖ ^ 2 := by
    apply tsum_congr
    intro ρ
    rw [hxy, inner_add_right, hzero ρ.1 ρ.2, zero_add]
  have htb := (canonical_positive_analysis_finite_tail_bound t ht F y).2
  rw [canonical_positive_analysis_tail_identity] at htb
  have hsmall := mul_le_mul_of_nonneg_right
    (htail.le.trans (min_le_right ε c)) (sq_nonneg ‖y‖)
  have hmargin : canonicalSharpMargin t ht S x = canonicalSharpMargin t ht S y := by
    rw [hxy]
    exact canonical_sharp_margin_add_maximizer t ht S z y hz
  change _ ≤ canonicalSharpMargin t ht S x
  rw [htailx, hmargin]
  exact htb.trans (hsmall.trans (hgap y hy))
