-- Prove2me | solution 2 for AvramDividend.Classical.chat04_shifted_random_reserve_upper_exit_right_interval
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:34:59.326533+00:00
-- url     : https://prove2.me/submissions/d6d66564-fa30-44dd-832c-d94fb2a1e82d

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_right_interval

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b t : ℝ≥0)
    (h : a < H ω + (X.X (b + t) ω - X.X b ω)) :
    ∃ u : ℝ≥0, b + t < u ∧
      ∀ v : ℝ≥0, b + t ≤ b + v → b + v < u →
        a < H ω + (X.X (b + v) ω - X.X b ω) := by
  obtain ⟨u, hu, hs⟩ := chat03_strict_upper_exit_right_interval X ω (b + t)
    (a - H ω + X.X b ω) (by linarith)
  refine ⟨u, hu, fun v h1 h2 => ?_⟩
  have := hs (b + v) h1 h2
  linarith
