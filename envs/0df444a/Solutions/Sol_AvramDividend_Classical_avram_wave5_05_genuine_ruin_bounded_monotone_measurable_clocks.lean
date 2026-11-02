-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_genuine_ruin_bounded_monotone_measurable_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:39:37.913183+00:00
-- url     : https://prove2.me/submissions/fdb8148c-fc00-4d93-9603-4614476ffaed

import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Truncate the genuine controlled ruin time by an increasing sequence of
deterministic integer horizons; retain source-path measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    (∀ n : ℕ,
        Measurable (fun ω : Ω =>
          min (ruinTime X x D ω) (n : ℝ≥0∞))) ∧
    (∀ ω : Ω,
        Monotone (fun n : ℕ =>
          min (ruinTime X x D ω) (n : ℝ≥0∞))) ∧
    (∀ ω : Ω,
        (⨆ n : ℕ, min (ruinTime X x D ω) (n : ℝ≥0∞)) =
          ruinTime X x D ω) := by
  constructor
  · intro n
    exact (ruinTime_measurable X x D hD).min measurable_const
  constructor
  · intro ω i j hij
    exact min_le_min_left _ (by exact_mod_cast hij)
  · intro ω
    calc
      (⨆ n : ℕ, min (ruinTime X x D ω) (n : ℝ≥0∞))
          = (ruinTime X x D ω) ⊓ (⨆ n : ℕ, (n : ℝ≥0∞)) := by
              rw [inf_iSup_eq]
      _ = ruinTime X x D ω := by simp [ENNReal.iSup_natCast]
