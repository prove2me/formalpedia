-- Prove2me | solution 1 for ConnesGreen.canonical_supported_neutral_zero_small_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T05:36:02.286214+00:00
-- url     : https://prove2.me/submissions/42414026-c52d-4a3c-ad8e-35b946b7557a

import Theorems.Thm_ConnesGreen_weil_positive_small_support
import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
theorem canonical_negative_analysis_partition (t : ℝ) (ht : 0 < t)
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

theorem solution (T : ℝ) (hT : 0 < T)
    (hTr : T ≤ positiveSupportRadius) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest T g)
    (hn : ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 = 0) : g = 0 := by
  have hw := ConnesGreen.weil_positive_small_support T hT.le hTr g hg
  have hf := ConnesGreen.canonical_signed_actor_arithmetic T hT g hg
  have hp := canonical_negative_analysis_partition T hT S (sourceEmbed T (problemOneL g))
  have hL : 0 ≤ ∫ s : ℝ, ‖g s‖ ^ 2 := integral_nonneg (fun s => sq_nonneg _)
  have hzero : (∫ s : ℝ, ‖g s‖ ^ 2) = 0 := by
    nlinarith [sq_nonneg ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖]
  have hi : Integrable (fun s => ‖g s‖ ^ 2) :=
    (hg.1.1.continuous.norm.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two, Pi.mul_apply] using hg.1.2.norm.mul_right (f' := fun s => ‖g s‖))
  have hae := (integral_eq_zero_iff_of_nonneg (fun s => sq_nonneg ‖g s‖) hi).mp hzero
  have he := ((hg.1.1.continuous.norm.pow 2).ae_eq_iff_eq volume continuous_const).mp hae
  ext s
  have hs := congrFun he s
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
