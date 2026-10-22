-- Prove2me | solution 1 for BirkhoffGlobalSection.saddle_center_arbitrarily_long_residence
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-01T20:42:05.759233+00:00
-- url     : https://prove2.me/submissions/001a4863-2d6d-4458-8d36-44eb4db7aa45

import Theorems.Thm_BirkhoffGlobalSection_saddle_center_slow_escape_segment
import Theorems.Thm_BirkhoffGlobalSection_saddle_center_no_short_subcritical_orbits

open BirkhoffGlobalSection

theorem solution
    (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U)
    (L : ℝ) (hL : 0 < L) :
    ∃ V : Set Phase, IsOpen V ∧ V ⊆ U ∧
      (![1 / 2, 0, 0, 0] : Phase) ∈ V ∧ (![-(1 / 2), 0, 0, 0] : Phase) ∈ V ∧
      ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
        ∀ μ c : ℝ, 0 < μ → μ < 1 →
          |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
          ∀ (x : ℝ → Phase) (T : ℝ),
            IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
              (leftEnergyComponent μ c) x T →
            (∃ t : ℝ, x t ∈ V) →
            L < T ∧ ∃ a : ℝ, ∀ t ∈ Set.Icc a (a + L), x t ∈ U := by
  obtain ⟨V₁, hV₁o, hV₁U, hV₁p, hV₁m, ε₁, η₁, hε₁, hη₁, hslow⟩ :=
    saddle_center_slow_escape_segment U hU hplus hminus L hL
  obtain ⟨V₂, hV₂o, hV₂U, hV₂p, hV₂m, ε₂, η₂, hε₂, hη₂, hperiod⟩ :=
    saddle_center_no_short_subcritical_orbits U hU hplus hminus L hL
  refine ⟨V₁ ∩ V₂, hV₁o.inter hV₂o, Set.inter_subset_left.trans hV₁U,
    ⟨hV₁p, hV₂p⟩, ⟨hV₁m, hV₂m⟩,
    min ε₁ ε₂, min η₁ η₂, lt_min hε₁ hε₂, lt_min hη₁ hη₂, ?_⟩
  intro μ c hμ0 hμ1 hμ hc hsub x T hx hvisit
  have hμ₁ : |μ - 1 / 2| < ε₁ := lt_of_lt_of_le hμ (min_le_left _ _)
  have hμ₂ : |μ - 1 / 2| < ε₂ := lt_of_lt_of_le hμ (min_le_right _ _)
  have hc₁ : c < 2 + η₁ :=
    lt_of_lt_of_le hc (add_le_add (le_refl (2 : ℝ)) (min_le_left _ _))
  have hc₂ : c < 2 + η₂ :=
    lt_of_lt_of_le hc (add_le_add (le_refl (2 : ℝ)) (min_le_right _ _))
  obtain ⟨t₀, ht₀⟩ := hvisit
  exact ⟨hperiod μ c hμ0 hμ1 hμ₂ hc₂ hsub x T hx ⟨t₀, ht₀.2⟩,
    hslow μ c hμ0 hμ1 hμ₁ hc₁ hsub x T hx ⟨t₀, ht₀.1⟩⟩
