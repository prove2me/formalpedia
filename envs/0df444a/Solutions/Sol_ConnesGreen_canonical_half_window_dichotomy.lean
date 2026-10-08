-- Prove2me | solution 1 for ConnesGreen.canonical_half_window_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T05:52:38.014999+00:00
-- url     : https://prove2.me/submissions/644314e2-d183-41be-883c-f82982838a47

import Theorems.Thm_ConnesGreen_positiveSupportRadius_positive
import Theorems.Thm_ConnesGreen_canonical_picard_half_small_support
import Theorems.Thm_ConnesGreen_canonicalPicardMarker_window_antitone
import Theorems.Thm_ConnesGreen_canonical_picard_half_of_all_smaller_windows
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
theorem solution (S : Finset CriticalZeros) :
    (∀ T : ℝ, ∀ hT : 0 < T, (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ∨
    ∃ c : ℝ, positiveSupportRadius ≤ c ∧ (∀ T : ℝ, ∀ hT : 0 < T, ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔ T ≤ c) := by
  classical
  by_cases hall : ∀ T : ℝ, ∀ hT : 0 < T, (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨b, hb, hbad⟩ := hall
    let G : Set ℝ := {T | 0 < T ∧ (1 / 2 : ℝ) •
      (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤
        positiveWindowPicardMarker T S}
    have hr : positiveSupportRadius ∈ G := by
      refine ⟨positiveSupportRadius_positive, ?_⟩
      rw [positiveWindowPicardMarker_eq _ positiveSupportRadius_positive]
      exact canonical_picard_half_small_support _ positiveSupportRadius_positive le_rfl S
    have hne : G.Nonempty := ⟨positiveSupportRadius, hr⟩
    have hbounded : BddAbove G := by
      refine ⟨b, ?_⟩
      intro T hTG
      by_contra hn
      have hhalf := hTG.2
      rw [positiveWindowPicardMarker_eq T hTG.1] at hhalf
      exact hbad (hhalf.trans (canonicalPicardMarker_window_antitone b T hb hTG.1 (le_of_not_ge hn) S))
    let c := sSup G
    have hrc : positiveSupportRadius ≤ c := le_csSup hbounded hr
    have hc : 0 < c := positiveSupportRadius_positive.trans_le hrc
    have hbelow : ∀ T : ℝ, ∀ hT : 0 < T, T < c →
        (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S := by
      intro T hT hTc
      obtain ⟨t, htG, hTt⟩ := exists_lt_of_lt_csSup hne hTc
      have hh := htG.2
      rw [positiveWindowPicardMarker_eq t htG.1] at hh
      exact hh.trans (canonicalPicardMarker_window_antitone T t hT htG.1 hTt.le S)
    have hclosed := canonical_picard_half_of_all_smaller_windows c hc S hbelow
    refine ⟨c, hrc, ?_⟩
    intro T hT
    constructor
    · intro hhalf
      apply le_csSup hbounded
      refine ⟨hT, ?_⟩
      rwa [positiveWindowPicardMarker_eq T hT]
    · intro hTc
      rcases lt_or_eq_of_le hTc with hlt | heq
      · exact hbelow T hT hlt
      · subst T
        exact hclosed
