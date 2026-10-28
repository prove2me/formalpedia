-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_random_reserve_lower_exit_right_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:48:53.904535+00:00
-- url     : https://prove2.me/submissions/cde59aab-a944-4498-9e69-702b0de4062c

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat03_strict_lower_exit_right_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A strictly ruined shifted reserve stays ruined throughout a right interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (b t : ℝ≥0)
    (h : H ω + (X.X (b + t) ω - X.X b ω) < 0) :
    ∃ u : ℝ≥0, b + t < u ∧
      ∀ v : ℝ≥0, b + t ≤ b + v → b + v < u →
        H ω + (X.X (b + v) ω - X.X b ω) < 0 := by
  have hOrig : X.X (b + t) ω < X.X b ω - H ω := by linarith
  obtain ⟨u, hu, hPersist⟩ :=
    chat03_strict_lower_exit_right_interval
      X ω (b + t) (X.X b ω - H ω) hOrig
  refine ⟨u, hu, ?_⟩
  intro v htv hvu
  have hBelow := hPersist (b + v) htv hvu
  linarith
