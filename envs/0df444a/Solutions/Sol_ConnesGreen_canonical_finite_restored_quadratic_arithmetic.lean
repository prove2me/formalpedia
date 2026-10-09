-- Prove2me | solution 1 for ConnesGreen.canonical_finite_restored_quadratic_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T14:10:13.671978+00:00
-- url     : https://prove2.me/submissions/6dd21c03-32a3-4c8b-992c-051e7744f597

import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Theorems.Thm_ConnesGreen_actual_physical_test_norm
import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability WeilDefect.WDT13
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
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
theorem solution (t : ℝ) (ht : 0 < t)
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

