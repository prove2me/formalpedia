-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_random_reserve_upper_exit_right_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:34:19.024864+00:00
-- url     : https://prove2.me/submissions/d6832bf1-1be3-45eb-addb-d15761a8d5bd

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_right_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strict crossing above an upper barrier persists on a shifted right interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b t : ℝ≥0)
    (h : a < H ω + (X.X (b + t) ω - X.X b ω)) :
    ∃ u : ℝ≥0, b + t < u ∧
      ∀ v : ℝ≥0, b + t ≤ b + v → b + v < u →
        a < H ω + (X.X (b + v) ω - X.X b ω) := by
  have hOrig : a + X.X b ω - H ω < X.X (b + t) ω := by linarith
  obtain ⟨u, hu, hPersist⟩ :=
    chat03_strict_upper_exit_right_interval
      X ω (b + t) (a + X.X b ω - H ω) hOrig
  refine ⟨u, hu, ?_⟩
  intro v htv hvu
  have hAbove := hPersist (b + v) htv hvu
  linarith
