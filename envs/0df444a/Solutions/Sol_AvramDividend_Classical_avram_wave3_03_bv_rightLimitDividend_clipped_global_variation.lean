-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_rightLimitDividend_clipped_global_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:43:12.966986+00:00
-- url     : https://prove2.me/submissions/7e1597bc-06f1-4866-b2fb-7bc715649ba0

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine post-payment dividend path, frozen after a finite horizon,
    is globally BV even with continuous and time-zero right-atomic payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    BoundedVariationOn
      (fun t : ℝ => rightLimit D (min t.toNNReal T) ω) Set.univ := by
  have hr : Monotone (fun s : ℝ≥0 => rightLimit D s ω) :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω
  have hm : Monotone (fun t : ℝ => rightLimit D (min t.toNNReal T) ω) := by
    intro a b hab
    exact hr (min_le_min (Real.toNNReal_mono hab) le_rfl)
  have hmono : MonotoneOn
      (fun t : ℝ => rightLimit D (min t.toNNReal T) ω) Set.univ := by
    intro a ha b hb hab
    exact hm hab
  apply hmono.boundedVariationOn
  intro t ht
  have hz : 0 ≤ rightLimit D (min t.toNNReal T) ω := by
    have hd := hD.2.1 ω
      (show (0 : ℝ≥0) ≤ min t.toNNReal T from zero_le)
    have hright := dividendStrategy_le_rightLimit D hD ω (min t.toNNReal T)
    have h0 : 0 ≤ D (min t.toNNReal T) ω := by
      simpa only [hD.1 ω] using hd
    exact le_trans h0 hright
  rw [abs_of_nonneg hz]
  exact hr (min_le_right t.toNNReal T)
