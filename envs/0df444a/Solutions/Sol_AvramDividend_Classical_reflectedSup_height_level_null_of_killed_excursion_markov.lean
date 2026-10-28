-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_height_level_null_of_killed_excursion_markov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:42:07.713778+00:00
-- url     : https://prove2.me/submissions/c88ccf38-fe76-46f7-9ff5-071c7adc71b5

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_excursion_height_level_null_of_markov_bad_event
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : Measure Ω) (Q : Measure (ℝ≥0 → ℝ))
    (T ζ H : Ω → ℝ≥0) (x : ℝ≥0)
    (hAtLevel : ∀ ω : Ω, H ω = x →
      T ω < ζ ω ∧
      reflectedSup X (T ω) ω = (x : ℝ) ∧
      ∀ t : ℝ≥0, T ω ≤ t → t < ζ ω →
        reflectedSup X t ω ≤ (x : ℝ))
    (hRegQ : ∀ᵐ f ∂Q, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ f s < 0)
    (hKilledMarkov :
      n {ω : Ω | T ω < ζ ω ∧
        ¬ ∀ ε : ℝ≥0, 0 < ε →
          ∃ s : ℝ≥0, s < ε ∧
            X.X (T ω + s) ω - X.X (T ω) ω < 0} =
      n {ω : Ω | T ω < ζ ω} *
        Q {f : ℝ≥0 → ℝ | ¬ ∀ ε : ℝ≥0, 0 < ε →
          ∃ s : ℝ≥0, s < ε ∧ f s < 0}) :
    n {ω : Ω | H ω = x} = 0 := by
  apply excursion_height_level_null_of_markov_bad_event
    n Q
    (fun ω t => runningSup X t ω)
    (fun ω t => X.X t ω)
    T ζ H x
  · intro ω hω
    obtain ⟨hT, hHit, hMax⟩ := hAtLevel ω hω
    exact ⟨hT, (runningSup_monotone_and_path_le X ω).1,
      hHit, hMax⟩
  · exact hRegQ
  · exact hKilledMarkov
