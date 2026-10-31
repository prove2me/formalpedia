-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_truncated_dividend_global_boundedVariationOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:57:31.494381+00:00
-- url     : https://prove2.me/submissions/e0f90761-2805-48ac-95da-8dc6e9d95ca5

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    BoundedVariationOn
      (fun t : ℝ => D (min t.toNNReal T) ω) Set.univ := by
  have hm : Monotone (fun t : ℝ => D (min t.toNNReal T) ω) := by
    intro a b hab
    exact hD.2.1 ω (min_le_min (Real.toNNReal_mono hab) le_rfl)
  have hmono : MonotoneOn
      (fun t : ℝ => D (min t.toNNReal T) ω) Set.univ := by
    intro a ha b hb hab
    exact hm hab
  apply hmono.boundedVariationOn
  intro t ht
  have h0 : 0 ≤ D (min t.toNNReal T) ω := by
    have h := hD.2.1 ω
      (show (0 : ℝ≥0) ≤ min t.toNNReal T from zero_le)
    simpa only [hD.1 ω] using h
  rw [abs_of_nonneg h0]
  exact hD.2.1 ω (min_le_right t.toNNReal T)
