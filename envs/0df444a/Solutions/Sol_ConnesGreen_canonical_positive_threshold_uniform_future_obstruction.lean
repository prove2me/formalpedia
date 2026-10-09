-- Prove2me | solution 1 for ConnesGreen.canonical_positive_threshold_uniform_future_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T04:51:34.125683+00:00
-- url     : https://prove2.me/submissions/3d19bf26-295f-41a5-8956-35b40892635c

import Definitions.Def_ConnesGreen_sharp_certificate_threshold
import Theorems.Thm_ConnesGreen_canonical_selected_form_ge_overlap_shift
import Theorems.Thm_ConnesGreen_testVectorFamily_dense
import Theorems.Thm_ConnesGreen_actual_physical_test_norm
import Theorems.Thm_ConnesGreen_canonical_actor_test_norms_window_independent
import Theorems.Thm_ConnesGreen_canonical_threshold_window_mono
import Theorems.Thm_ConnesGreen_canonical_no_finite_certificate_below_threshold
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability
namespace ConnesGreen
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
theorem canonical_threshold_le_iff_supported_tests (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (a : ℝ) (ha : 0 ≤ a) :
    canonicalCertificateThreshold t ht S ≤ a ↔
    ∀ g : ℝ → ℂ, SupportedTest t g →
      -a * physicalTestEnergy g ≤
        ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
          ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 := by
  constructor
  · intro h g hg
    have hs := canonical_selected_form_ge_sharp_threshold t ht S
      (sourceEmbed t (problemOneL g))
    have he := actual_physical_test_norm t ht g hg
    change ‖sourceEmbed t (problemOneL g)‖ ^ 2 = physicalTestEnergy g at he
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg ‖sourceEmbed t (problemOneL g)‖)
    rw [← he]
    linarith
  · intro h
    have hb (x : Physical t) : -a * ‖x‖ ^ 2 ≤
        ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
          ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 := by
      refine (testVectorFamily_dense t ht).induction_on (p := fun x =>
        -a * ‖x‖ ^ 2 ≤ ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
          ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2) x ?_ ?_
      · exact isClosed_le (continuous_const.mul (continuous_norm.pow 2))
          (((canonicalPositiveSynthesis t ht).adjoint.continuous.norm.pow 2).sub
            ((canonicalSelectedSynthesis t ht S).adjoint.continuous.norm.pow 2))
      · intro g
        have he := actual_physical_test_norm t ht g.1 g.2
        change ‖sourceEmbed t (problemOneL g.1)‖ ^ 2 = physicalTestEnergy g.1 at he
        change -a * ‖sourceEmbed t (problemOneL g.1)‖ ^ 2 ≤ _
        rw [he]
        exact h g.1 g.2
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    by_cases hx : x = 0
    · simpa [hx] using ha
    · apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr
      have h := hb x
      linarith
end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (hp : 0 < canonicalCertificateThreshold t ht S) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ T : ℝ, ∀ hT : 0 < T, t ≤ T →
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ F : Finset CriticalZeros,
        ¬ 0 ≤ canonicalFiniteSelectedCorrection T hT S F δ := by
  refine ⟨canonicalCertificateThreshold t ht S / 2, half_pos hp, ?_⟩
  intro T hT htT δ hδ hle F
  apply canonical_no_finite_certificate_below_threshold T hT S δ hδ _ F
  have hm := canonical_threshold_window_mono t T ht hT htT S
  linarith
