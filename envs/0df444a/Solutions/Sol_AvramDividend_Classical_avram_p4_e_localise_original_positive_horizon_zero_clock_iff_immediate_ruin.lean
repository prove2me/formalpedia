-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_positive_horizon_zero_clock_iff_immediate_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:25:27.55416+00:00
-- url     : https://prove2.me/submissions/ba84582c-6d8d-4fae-b800-c0cbe30b49c8

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- At every strictly positive deterministic horizon, the true stopped clock is zero exactly at immediate ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) :
    ∀ ω, (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal = 0 ↔
      ruinTime X x D ω = 0 := by
  intro ω
  have hclock :=
    (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).1 ω
  constructor
  · intro hzero
    have hmin : min (ruinTime X x D ω) (n : ℝ≥0∞) = 0 := by
      calc
        min (ruinTime X x D ω) (n : ℝ≥0∞) =
            (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) :=
          hclock.symm
        _ = 0 := by simp [hzero]
    by_contra hr
    have hRpos : (0 : ℝ≥0∞) < ruinTime X x D ω :=
      pos_iff_ne_zero.mpr hr
    have hNpos : (0 : ℝ≥0∞) < (n : ℝ≥0∞) := by
      exact_mod_cast hn
    have hminpos : (0 : ℝ≥0∞) <
        min (ruinTime X x D ω) (n : ℝ≥0∞) :=
      lt_min hRpos hNpos
    exact (ne_of_gt hminpos) hmin
  · intro hr
    simp [hr]
