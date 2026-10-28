-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_height_level_null_of_ae_posthit_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:56:02.860515+00:00
-- url     : https://prove2.me/submissions/a711c338-93a5-4129-aef0-47799c401d0a

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_reflected_excursion_height_level_null_of_ae_negative_on_hitting
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
    (n : Measure Ω) (T ζ H : Ω → ℝ≥0) (x : ℝ≥0)
    (hAtLevel : ∀ ω : Ω, H ω = x →
      T ω < ζ ω ∧
      reflectedSup X (T ω) ω = (x : ℝ) ∧
      ∀ t : ℝ≥0, T ω ≤ t → t < ζ ω →
        reflectedSup X t ω ≤ (x : ℝ))
    (hNegOnHitAE : ∀ᵐ ω ∂n, T ω < ζ ω →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧
          X.X (T ω + s) ω < X.X (T ω) ω) :
    n {ω : Ω | H ω = x} = 0 := by
  apply reflected_excursion_height_level_null_of_ae_negative_on_hitting
    n
    (fun ω t => runningSup X t ω)
    (fun ω t => X.X t ω)
    T ζ H x
  · intro ω hω
    obtain ⟨hT, hHit, hMax⟩ := hAtLevel ω hω
    exact ⟨hT, (runningSup_monotone_and_path_le X ω).1,
      hHit, hMax⟩
  · exact hNegOnHitAE
