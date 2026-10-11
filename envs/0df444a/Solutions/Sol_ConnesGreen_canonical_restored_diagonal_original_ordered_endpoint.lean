-- Prove2me | solution 1 for ConnesGreen.canonical_restored_diagonal_original_ordered_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T18:20:18.73165+00:00
-- url     : https://prove2.me/submissions/935dd269-7a71-41d3-bc21-ef2247a22c71

import Theorems.Thm_ConnesGreen_canonical_nested_diagonal_actual_tail_marker_recovery
import Theorems.Thm_WeilDefect_MarkerStability_finite_selected_marker_norm_limit
import Theorems.Thm_ConnesGreen_canonical_actual_zero_support_right_limit
import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
lemma ConnesGreen.tendsto_of_vanishing_marker_error
    {E : Type*} [NormedAddCommGroup E] (A B : ℕ → E) (G : E) (ε : ℕ → ℝ)
    (hA : Tendsto A atTop (nhds G)) (hε : Tendsto ε atTop (nhds 0))
    (hb : ∀ n, ‖A n - B n‖ ≤ ε n) : Tendsto B atTop (nhds G) := by
  apply hA.congr_dist
  apply squeeze_zero (fun _ => dist_nonneg)
  · intro n
    simpa only [dist_eq_norm] using hb n
  · exact hε

lemma ConnesGreen.canonical_restored_sequence_picard_limit
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (F : ℕ → Finset CriticalZeros) (μ ε : ℕ → ℝ)
    (hμ : ∀ n, 0 < μ n) (hμlim : Tendsto μ atTop (nhds 0))
    (hεlim : Tendsto ε atTop (nhds 0))
    (hb : ∀ n,
      ‖canonicalRegularizedMarker t ht S (μ n) -
        marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
          (canonicalSelectedSynthesis t ht S)‖ ≤ ε n) :
    Tendsto (fun n => marker (canonicalPositiveCovariance t ht + μ n • 1 -
      canonicalTailCovariance t ht (F n)) (canonicalSelectedSynthesis t ht S))
      atTop (nhds (canonicalPicardMarker t ht S)) := by
  have hμwithin : Tendsto μ atTop (nhdsWithin 0 (Ioi (0 : ℝ))) :=
    tendsto_nhdsWithin_iff.mpr ⟨hμlim, Eventually.of_forall hμ⟩
  exact tendsto_of_vanishing_marker_error
    (fun n => canonicalRegularizedMarker t ht S (μ n)) _ _ ε
    ((canonicalPicardMarker_spec t ht S).2.2.2.comp hμwithin) hεlim hb
theorem solution
    (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (K : ℕ → Finset CriticalZeros) (μ ε : ℕ → ℝ)
    (hμ : ∀ n, 0 < μ n) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n < 1)
    (hμlim : Tendsto μ atTop (nhds 0)) (hεlim : Tendsto ε atTop (nhds 0)) :
    ∃ F : ℕ → Finset CriticalZeros, Monotone F ∧
      (∀ n, S ⊆ F n ∧ K n ⊆ F n ∧ (∀ τ ∈ F n, reflectedZero τ ∈ F n)) ∧
      (∀ n, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({τ : CriticalZeros // τ ∉ (F n)}, ℂ) →L[ℂ] Physical t,
          (∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
            positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht (F n)‖ < ε n ∧
          (∀ ν : ℝ, μ n ≤ ν →
            ‖canonicalTailCovariance t ht (F n)‖ ≤ ε n * ν ∧
            IsStrictlyPositive (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n)) ∧
            0 ≤ marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S) ∧
            ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ ≤ ε n) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            Summable (fun τ : CriticalZeros => ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
            (∑' τ : CriticalZeros, ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε n)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
          ‖canonicalTailCovariance t ht (F n)‖ < δ ∧
          (∀ ν : ℝ, μ n ≤ ν → ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ < δ) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            (∑' τ : CriticalZeros, ‖if τ ∈ F n then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < δ)) ∧
      (∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        Tendsto (fun n => marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S))
          atTop (nhds (canonicalPicardMarker t ht S))) ∧
      (∀ c : ℝ, ∀ hc : 0 ≤ c, c < T → ∀ δ : ℝ, 0 < δ →
        ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
          ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
            ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
              ‖marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S) - canonicalSupportRightMarker c hc S‖ < δ) := by
  obtain ⟨F, hmono, hrequests, hstage, huniform⟩ :=
    canonical_nested_diagonal_actual_tail_marker_recovery T hT S K μ ε hμ hε hε1 hμlim hεlim
  have hinner : ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        Tendsto (fun n => marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S))
          atTop (nhds (canonicalPicardMarker t ht S)) := by
    intro t ht htT
    apply canonical_restored_sequence_picard_limit t ht S F μ ε hμ hμlim hεlim
    intro n
    obtain ⟨Ptail, hcols, hsmall, hband, hactual⟩ := hstage n t ht htT
    exact (hband (μ n) le_rfl).2.2.2
  refine ⟨F, hmono, hrequests, hstage, huniform, hinner, ?_⟩
  intro c hc hcT δ hδ
  have hhalf : 0 < δ / 2 := half_pos hδ
  obtain ⟨d₀, hd₀, houter⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    (canonicalSupportRightMarker_spec c hc S).2.2.2 (δ / 2) hhalf
  let d : ℝ := min d₀ (T - c)
  have hd : 0 < d := lt_min hd₀ (sub_pos.mpr hcT)
  have hdT : c + d ≤ T := by
    have hm : d ≤ T - c := min_le_right _ _
    linarith
  refine ⟨d, hd, hdT, ?_⟩
  intro t ht hct htd
  have htT : t ≤ T := (le_of_lt htd).trans hdT
  have hdist : dist t c < d₀ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hct)]
    have hm : d ≤ d₀ := min_le_left _ _
    linarith
  have ho : ‖canonicalPicardMarker t ht S - canonicalSupportRightMarker c hc S‖ < δ / 2 := by
    simpa only [positiveWindowPicardMarker_eq t ht S, dist_eq_norm] using houter hct hdist
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hinner t ht htT) (δ / 2) hhalf
  refine ⟨N, ?_⟩
  intro n hn
  have hi : ‖marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S) - canonicalPicardMarker t ht S‖ < δ / 2 := by
    simpa only [dist_eq_norm] using hN n hn
  calc
    _ ≤ ‖marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S) - canonicalPicardMarker t ht S‖ +
      ‖canonicalPicardMarker t ht S - canonicalSupportRightMarker c hc S‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
          (canonicalSelectedSynthesis t ht S))
        (canonicalPicardMarker t ht S) (canonicalSupportRightMarker c hc S)
    _ < δ := by linarith
