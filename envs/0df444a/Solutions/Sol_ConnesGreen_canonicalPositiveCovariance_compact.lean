-- Prove2me | solution 1 for ConnesGreen.canonicalPositiveCovariance_compact
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T05:54:11.716176+00:00
-- url     : https://prove2.me/submissions/0ce713b4-0d2f-4c54-8887-0e80c4705b23

import Definitions.Def_ConnesGreen_selected_loss_covariance
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

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
theorem canonical_finite_positive_analysis_energy (t : ℝ) (F : Finset CriticalZeros)
    (x : Physical t) :
    ‖(canonicalFinitePositiveSynthesis t F).adjoint x‖ ^ 2 =
      ∑ ρ ∈ F, ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2 := by
  rw [canonicalFinitePositiveSynthesis, columnSynthesis_adjoint_norm_sq]
  exact Finset.tsum_subtype F (fun ρ : CriticalZeros =>
    ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2)
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
private theorem real_smul_one_selfAdjoint (t : ℝ) (a : ℝ) :
    IsSelfAdjoint (a • (1 : Physical t →L[ℂ] Physical t)) := by
  change IsSelfAdjoint ((a : ℂ) • (1 : Physical t →L[ℂ] Physical t))
  apply IsSelfAdjoint.smul
  · change (starRingEnd ℂ) (a : ℂ) = (a : ℂ)
    simp
  · exact ContinuousLinearMap.isPositive_one.isSelfAdjoint
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
theorem canonical_positive_covariance_finite_error (t : ℝ) (ht : 0 < t)
    (F : Finset CriticalZeros) :
    ‖canonicalPositiveCovariance t ht -
      canonicalFinitePositiveSynthesis t F ∘L (canonicalFinitePositiveSynthesis t F).adjoint‖ ≤
    ∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
      ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2 := by
  let E := canonicalPositiveCovariance t ht -
    canonicalFinitePositiveSynthesis t F ∘L (canonicalFinitePositiveSynthesis t F).adjoint
  let b := ∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
    ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2
  have hb : 0 ≤ b := tsum_nonneg (fun _ => sq_nonneg _)
  have hs : IsSelfAdjoint E :=
    (ContinuousLinearMap.isPositive_self_comp_adjoint (canonicalPositiveSynthesis t ht)).isSelfAdjoint.sub
      (ContinuousLinearMap.isPositive_self_comp_adjoint (canonicalFinitePositiveSynthesis t F)).isSelfAdjoint
  have he (x : Physical t) : RCLike.re ⟪E x, x⟫_ℂ =
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
        ∑ ρ ∈ F, ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2 := by
    have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left x
    have hf := (canonicalFinitePositiveSynthesis t F).adjoint.apply_norm_sq_eq_inner_adjoint_left x
    simp only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply] at hp hf
    simp only [E, canonicalPositiveCovariance, sub_apply, inner_sub_left, map_sub,
      ContinuousLinearMap.comp_apply]
    rw [← hp, ← hf, canonical_finite_positive_analysis_energy]
  have hpos : E.IsPositive := by
    rw [ContinuousLinearMap.isPositive_def']
    refine ⟨hs, ?_⟩
    intro x
    change 0 ≤ RCLike.re ⟪E x, x⟫_ℂ
    rw [he]
    exact (canonical_positive_analysis_finite_tail_bound t ht F x).1
  have hE : 0 ≤ E := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    exact hpos
  apply (CStarAlgebra.norm_le_iff_le_algebraMap E hb hE).mpr
  rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.le_def,
    ContinuousLinearMap.isPositive_def']
  refine ⟨(real_smul_one_selfAdjoint t b).sub hs, ?_⟩
  intro x
  change 0 ≤ RCLike.re ⟪(b • (1 : Physical t →L[ℂ] Physical t) - E) x, x⟫_ℂ
  have hx : RCLike.re ⟪(b • (1 : Physical t →L[ℂ] Physical t)) x, x⟫_ℂ = b * ‖x‖ ^ 2 := by
    change RCLike.re ⟪(b : ℂ) • x, x⟫_ℂ = _
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [Complex.star_def, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  rw [sub_apply, inner_sub_left, map_sub, hx, he]
  exact sub_nonneg.mpr (canonical_positive_analysis_finite_tail_bound t ht F x).2
end ConnesGreen
theorem solution (t : ℝ) (ht : 0 < t) :
    IsCompactOperator (canonicalPositiveCovariance t ht) := by
  have hlim : Tendsto (fun F : Finset CriticalZeros =>
      canonicalFinitePositiveSynthesis t F ∘L (canonicalFinitePositiveSynthesis t F).adjoint)
      atTop (nhds (canonicalPositiveCovariance t ht)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have htail := (tendsto_order.mp (tendsto_tsum_compl_atTop_zero
      (fun ρ : CriticalZeros =>
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ‖ ^ 2))).2 ε hε
    filter_upwards [htail] with F hF
    rw [dist_eq_norm, norm_sub_rev]
    exact (canonical_positive_covariance_finite_error t ht F).trans_lt hF
  apply isCompactOperator_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro F
  letI : FiniteDimensional ℂ (ℓ²({ρ : CriticalZeros // ρ ∈ F}, ℂ)) := finite_coefficients F
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (canonicalFinitePositiveSynthesis t F)).comp_clm
      (canonicalFinitePositiveSynthesis t F).adjoint
