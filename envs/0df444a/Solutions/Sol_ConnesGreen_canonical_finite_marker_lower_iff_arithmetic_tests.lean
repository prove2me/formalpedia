-- Prove2me | solution 1 for ConnesGreen.canonical_finite_marker_lower_iff_arithmetic_tests
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T14:09:51.903105+00:00
-- url     : https://prove2.me/submissions/95f35eee-0b15-4020-ab9f-5fea4ef2324a

import Theorems.Thm_WeilDefect_MarkerStability_half_bound_iff_covariance_le
import Theorems.Thm_WeilDefect_MarkerStability_marker_lower_iff_cost_upper
import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Theorems.Thm_ConnesGreen_actual_physical_test_norm
import Theorems.Thm_ConnesGreen_covariance_le_iff_original_tests
import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability WeilDefect.WDT13
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
section
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
private theorem inverse_helper (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (c : ℝ) (hc : 0 < c) :
    operatorInverse (c • A) = c⁻¹ • operatorInverse A := by
  have hunit := (hA.smul hc).isUnit
  have hright : (c • A) * (c⁻¹ • operatorInverse A) = 1 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_inv_cancel₀ hc.ne', one_smul]
    exact Ring.mul_inverse_cancel A hA.isUnit
  calc
    operatorInverse (c • A) = operatorInverse (c • A) * 1 := (mul_one _).symm
    _ = operatorInverse (c • A) * ((c • A) * (c⁻¹ • operatorInverse A)) := by rw [hright]
    _ = (operatorInverse (c • A) * (c • A)) * (c⁻¹ • operatorInverse A) := (mul_assoc _ _ _).symm
    _ = c⁻¹ • operatorInverse A := by
      rw [show operatorInverse (c • A) * (c • A) = 1 from Ring.inverse_mul_cancel _ hunit,
        one_mul]

private theorem cost_smul_helper (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (c : ℝ) (hc : 0 < c) :
    selectedCost (c • A) N = c⁻¹ • selectedCost A N := by
  rw [selectedCost, inverse_helper A hA c hc]
  ext x
  simp [selectedCost]

private theorem cost_one_helper (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : selectedCost A N ≤ 1 ↔ N ∘L N.adjoint ≤ A := by
  have hh : (1 / 2 : ℝ) • (1 : K →L[ℂ] K) ≤ marker A N ↔ selectedCost A N ≤ 1 := by
    convert marker_lower_iff_cost_upper A hA N (1 / 2) (by norm_num) using 1 <;> norm_num
  exact hh.symm.trans (half_bound_iff_covariance_le A hA N)
private theorem cost_scaled_helper (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (κ : ℝ) (hκ : 0 < κ) :
    selectedCost A N ≤ κ • (1 : K →L[ℂ] K) ↔ N ∘L N.adjoint ≤ κ • A := by
  rw [← cost_one_helper (κ • A) (hA.smul hκ) N,
    cost_smul_helper A hA N κ hκ]
  constructor
  · intro h
    have hi := smul_le_smul_of_nonneg_left h (inv_pos.mpr hκ).le
    simpa only [smul_smul, inv_mul_cancel₀ hκ.ne', one_smul] using hi
  · intro h
    have hi := smul_le_smul_of_nonneg_left h hκ.le
    simpa only [smul_smul, mul_inv_cancel₀ hκ.ne', one_smul] using hi

end
private theorem partition_helper (t : ℝ) (ht : 0 < t)
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

private theorem norm_helper (t : ℝ) (ht : 0 < t) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    ‖sourceEmbed t (problemOneL g)‖ ^ 2 = ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) + (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2)) := by
  exact actual_physical_test_norm t ht g hg
theorem scaled_helper
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) (N : K →L[ℂ] H)
    (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    β • (1 : K →L[ℂ] K) ≤ marker A N ↔ N ∘L N.adjoint ≤ (β⁻¹ - 1) • A := by
  have hκ : 0 < β⁻¹ - 1 := by
    have hi : 1 < β⁻¹ := (one_lt_inv₀ hβ).mpr hβ1
    linarith
  rw [marker_lower_iff_cost_upper A hA N β hβ,
    cost_scaled_helper A hA N (β⁻¹ - 1) hκ]

theorem quadratic_helper (t : ℝ) (ht : 0 < t)
    (F : Finset CriticalZeros) (ε : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    RCLike.re ⟪(canonicalPositiveCovariance t ht + ε • 1 - canonicalTailCovariance t ht F)
      (sourceEmbed t (problemOneL g)), sourceEmbed t (problemOneL g)⟫_ℂ =
      (weilDistribution (conv g (starInv g))).re +
      ‖(canonicalSelectedSynthesis t ht F).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
      ε * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) + (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2)) := by
  let x := sourceEmbed t (problemOneL g)
  have he := canonical_signed_actor_arithmetic t ht g hg
  have hpart := partition_helper t ht F x
  have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  have hb := (canonicalBackgroundSynthesis t ht F).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint] at hp hb
  change RCLike.re ⟪(canonicalPositiveCovariance t ht + ε • 1 - canonicalTailCovariance t ht F) x, x⟫_ℂ = _
  have hr : RCLike.re ⟪(ε • (1 : Physical t →L[ℂ] Physical t)) x, x⟫_ℂ = ε * ‖x‖ ^ 2 := by
    letI := InnerProductSpace.rclikeToReal ℂ (Physical t)
    simp only [ContinuousLinearMap.smul_apply, one_apply_eq_self]
    rw [← real_inner_eq_re_inner ℂ]
    exact (real_inner_smul_left x x ε).trans
      (congrArg (fun r : ℝ => ε * r) (real_inner_self_eq_norm_sq x))
  simp only [sub_apply, add_apply, inner_sub_left, inner_add_left, map_sub, map_add]
  rw [hr]
  change RCLike.re ⟪(canonicalPositiveSynthesis t ht ∘L (canonicalPositiveSynthesis t ht).adjoint) x, x⟫_ℂ +
    ε * ‖x‖ ^ 2 - RCLike.re ⟪(canonicalBackgroundSynthesis t ht F ∘L
      (canonicalBackgroundSynthesis t ht F).adjoint) x, x⟫_ℂ = _
  rw [← hp, ← hb, norm_helper t ht g hg]
  dsimp [x] at *
  linarith

theorem solution (t : ℝ) (ht : 0 < t)
    (S F : Finset CriticalZeros) (ε β : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (hA : IsStrictlyPositive (canonicalPositiveCovariance t ht + ε • 1 -
      canonicalTailCovariance t ht F)) :
    β • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ marker (canonicalPositiveCovariance t ht + ε • 1 - canonicalTailCovariance t ht F) (canonicalSelectedSynthesis t ht S) ↔
    ∀ g : ℝ → ℂ, SupportedTest t g →
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
      (β⁻¹ - 1) * ((weilDistribution (conv g (starInv g))).re +
        ‖(canonicalSelectedSynthesis t ht F).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
        ε * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) + (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))) := by
  rw [scaled_helper _ hA _ β hβ hβ1]
  have hs0 := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hA.nonneg).isSelfAdjoint
  have hs : IsSelfAdjoint ((β⁻¹ - 1) • (canonicalPositiveCovariance t ht + ε • 1 -
      canonicalTailCovariance t ht F)) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change ⟪(β⁻¹ - 1) • ((canonicalPositiveCovariance t ht + ε • 1 - canonicalTailCovariance t ht F) x), y⟫_ℂ =
      ⟪x, (β⁻¹ - 1) • ((canonicalPositiveCovariance t ht + ε • 1 - canonicalTailCovariance t ht F) y)⟫_ℂ
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    have hij : ⟪(canonicalPositiveCovariance t ht + ε • 1 - canonicalTailCovariance t ht F) x, y⟫_ℂ =
      ⟪x, (canonicalPositiveCovariance t ht + ε • 1 - canonicalTailCovariance t ht F) y⟫_ℂ := hs0.isSymmetric x y
    have hstar : (starRingEnd ℂ) ((β⁻¹ - 1 : ℝ) : ℂ) = ((β⁻¹ - 1 : ℝ) : ℂ) := by simp
    erw [hstar]
    exact congrArg (fun z : ℂ => ((β⁻¹ - 1 : ℝ) : ℂ) * z) hij

  rw [covariance_le_iff_original_tests t ht _ hs _]
  apply forall_congr'
  intro g
  apply imp_congr_right
  intro hg
  have hr : RCLike.re ⟪((β⁻¹ - 1) • (canonicalPositiveCovariance t ht + ε • 1 -
      canonicalTailCovariance t ht F)) (sourceEmbed t (problemOneL g)),
      sourceEmbed t (problemOneL g)⟫_ℂ =
      (β⁻¹ - 1) * RCLike.re ⟪(canonicalPositiveCovariance t ht + ε • 1 -
      canonicalTailCovariance t ht F) (sourceEmbed t (problemOneL g)),
      sourceEmbed t (problemOneL g)⟫_ℂ := by
    letI := InnerProductSpace.rclikeToReal ℂ (Physical t)
    simp only [← real_inner_eq_re_inner ℂ, ContinuousLinearMap.smul_apply, real_inner_smul_left]
  rw [hr, quadratic_helper t ht F ε g hg]

