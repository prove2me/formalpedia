-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva100_original_positive_ruin_clipped_physical_clock_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:47:25.371206+00:00
-- url     : https://prove2.me/submissions/f3d188a6-4dc7-4c39-b5fd-32ca725a14d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (S : ℝ≥0) (hS : 0 < S)
    (hR : ruinTime X x D ω ≠ 0) :
    0 < (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal := by
  have hr : (0 : ℝ≥0∞) < ruinTime X x D ω :=
    (bot_lt_iff_ne_bot).2 hR
  have hs : (0 : ℝ≥0∞) < (S : ℝ≥0∞) := by exact_mod_cast hS
  have hmin : (0 : ℝ≥0∞) < min (ruinTime X x D ω) (S : ℝ≥0∞) :=
    (lt_min_iff).2 ⟨hr, hs⟩
  have htop : min (ruinTime X x D ω) (S : ℝ≥0∞) < ⊤ :=
    lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top
  exact ENNReal.toNNReal_pos_iff.mpr ⟨hmin, htop⟩
