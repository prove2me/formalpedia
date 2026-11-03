-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_source_truncated_clock_nnreal_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:23:45.148739+00:00
-- url     : https://prove2.me/submissions/399acfce-9d9a-41ac-80d4-63784bbdf82b

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    let τ : Ω → ℝ≥0 :=
      fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    (∀ ω, (τ ω : ℝ≥0∞) = min (ruinTime X x D ω) (n : ℝ≥0∞)) ∧
    (∀ ω, τ ω ≤ (n : ℝ≥0)) ∧
    (∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω) := by
  dsimp
  have hcast (ω : Ω) :
      (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0∞) =
        min (ruinTime X x D ω) (n : ℝ≥0∞)) := by
    apply ENNReal.coe_toNNReal
    have hlt : min (ruinTime X x D ω) (n : ℝ≥0∞) < ⊤ :=
      lt_of_le_of_lt (min_le_right (ruinTime X x D ω) (n : ℝ≥0∞)) (by simp)
    exact ne_of_lt hlt
  refine ⟨hcast, ?_, ?_⟩
  · intro ω
    apply (ENNReal.coe_le_coe).mp
    have hle := min_le_right (ruinTime X x D ω) (n : ℝ≥0∞)
    simpa [hcast ω] using hle
  · intro ω
    rw [hcast ω]
    exact min_le_left (ruinTime X x D ω) (n : ℝ≥0∞)
