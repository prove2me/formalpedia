-- Prove2me | solution 1 for ConnesGreen.canonical_selected_form_ge_overlap_shift
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T03:46:28.158389+00:00
-- url     : https://prove2.me/submissions/50f6db8d-dad9-403f-b557-76c1bc21e35b

import Definitions.Def_ConnesGreen_arithmetic_overlap_shift
import Theorems.Thm_ConnesGreen_weil_re_ge_overlap_shift_energy
import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Theorems.Thm_ConnesGreen_testVectorFamily_dense
import Theorems.Thm_ConnesGreen_actual_physical_test_norm
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability
namespace ConnesGreen
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
end ConnesGreen
theorem solution (R T : ℝ) (hT : 0 < T) (hTR : T ≤ R)
    (S : Finset CriticalZeros) (x : Physical T) :
    -arithmeticOverlapShift R * ‖x‖ ^ 2 ≤
      ‖(canonicalPositiveSynthesis T hT).adjoint x‖ ^ 2 - ‖(canonicalSelectedSynthesis T hT S).adjoint x‖ ^ 2 := by
  refine (testVectorFamily_dense T hT).induction_on (p := fun x =>
    -arithmeticOverlapShift R * ‖x‖ ^ 2 ≤
      ‖(canonicalPositiveSynthesis T hT).adjoint x‖ ^ 2 -
        ‖(canonicalSelectedSynthesis T hT S).adjoint x‖ ^ 2) x ?_ ?_
  · exact isClosed_le (continuous_const.mul (continuous_norm.pow 2))
      (((canonicalPositiveSynthesis T hT).adjoint.continuous.norm.pow 2).sub
        ((canonicalSelectedSynthesis T hT S).adjoint.continuous.norm.pow 2))
  · intro g
    have hgR : SupportedTest R g.1 := by
      refine ⟨g.2.1, ?_⟩
      intro s hs
      have h := g.2.2 hs
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hw := weil_re_ge_overlap_shift_energy R (le_trans hT.le hTR) g.1 hgR
    have ha := canonical_signed_actor_arithmetic T hT g.1 g.2
    have hn := canonical_negative_analysis_partition T hT S (sourceEmbed T (problemOneL g.1))
    have he := actual_physical_test_norm T hT g.1 g.2
    change -arithmeticOverlapShift R * ‖sourceEmbed T (problemOneL g.1)‖ ^ 2 ≤ _
    change ‖sourceEmbed T (problemOneL g.1)‖ ^ 2 = physicalTestEnergy g.1 at he
    rw [← he] at hw
    nlinarith [sq_nonneg ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g.1))‖]
