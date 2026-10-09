-- Prove2me | solution 1 for ConnesGreen.mathlib_RH_iff_cofinal_quartet_half_windows
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T17:36:36.122094+00:00
-- url     : https://prove2.me/submissions/5aed3e4a-6d08-4f8a-b6b2-6b4517b17f82

import Theorems.Thm_ConnesGreen_canonicalPicardMarker_window_antitone
import Theorems.Thm_ConnesGreen_canonical_quartet_last_inner_half_window
import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_original_selected_tests
import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Theorems.Thm_ConnesRZFrontier_weilPositive_iff_mathlib_RH
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_original_quartet
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
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
private theorem cofinal_helper (S : Finset CriticalZeros) :
    (∀ T : ℝ, ∀ hT : 0 < T,
      (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔
    (∀ B : ℝ, ∃ T : ℝ, ∃ hT : 0 < T, B < T ∧
      (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) := by
  constructor
  · intro h B
    let T := max B 0 + 1
    have hT : 0 < T := by dsimp [T]; linarith [le_max_right B 0]
    refine ⟨T, hT, ?_, h T hT⟩
    dsimp [T]
    linarith [le_max_left B 0]
  · intro h T hT
    obtain ⟨U, hU, hTU, hhalf⟩ := h T
    exact hhalf.trans (canonicalPicardMarker_window_antitone T U hT hU hTU.le S)

private theorem positive_helper
    (h : ∀ g : ℝ → ℂ, IsTest g → 0 ≤ (weilDistribution (conv g (starInv g))).re)
    (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S := by
  apply (canonical_picard_half_iff_original_selected_tests T hT S).mpr
  intro g hg
  change 0 ≤ ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 -
    ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2
  have ha := ConnesGreen.canonical_signed_actor_arithmetic T hT g hg
  have hp := partition_helper T hT S (sourceEmbed T (problemOneL g))
  have hw := h g hg.1
  have hb := sq_nonneg (‖(canonicalBackgroundSynthesis T hT S).adjoint
    (sourceEmbed T (problemOneL g))‖)
  linarith
private theorem all_windows_helper :
    RiemannHypothesis ↔ ∀ ρ : CriticalZeros, ∀ T : ℝ, ∀ hT : 0 < T,
      (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤
          canonicalPicardMarker T hT (quartet ρ) := by
  constructor
  · intro h ρ T hT
    exact positive_helper
      (ConnesRZFrontier.weilPositive_iff_mathlib_RH.mpr h) T hT (quartet ρ)
  · intro h
    apply riemannHypothesis_iff_zeros_in_strip_on_line.mpr
    intro s hz hlo hhi
    have hs : IsCriticalZero s := ⟨hz, hlo, hhi⟩
    by_contra hoff
    let ρ : CriticalZeros := ⟨s, hs⟩
    obtain ⟨c, _, hcut⟩ := canonical_quartet_last_inner_half_window ρ hoff
    let T := max c 0 + 1
    have hT : 0 < T := by dsimp [T]; linarith [le_max_right c 0]
    have hcT : c < T := by dsimp [T]; linarith [le_max_left c 0]
    exact (not_le_of_gt hcT) ((hcut T hT).mp (h ρ T hT))

theorem solution :
    RiemannHypothesis ↔ ∀ ρ : CriticalZeros, ∀ B : ℝ,
      ∃ T : ℝ, ∃ hT : 0 < T, B < T ∧
        (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤
            canonicalPicardMarker T hT (quartet ρ) := by
  rw [all_windows_helper]
  exact forall_congr' fun ρ => cofinal_helper (quartet ρ)

