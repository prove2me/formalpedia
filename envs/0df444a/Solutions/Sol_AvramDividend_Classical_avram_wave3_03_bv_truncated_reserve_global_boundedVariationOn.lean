-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_truncated_reserve_global_boundedVariationOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:29:27.701124+00:00
-- url     : https://prove2.me/submissions/efc6043b-1440-4b7c-8ac5-b3e66dc30dad

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_boundedVariationOn_compact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      BoundedVariationOn
        (fun t : ℝ≥0 => riskProcess X x D (min t T) ω) Set.univ := by
  filter_upwards [
    avram_wave3_03_bv_controlled_reserve_boundedVariationOn_compact X hX hBV x D hD
  ] with ω hω
  intro T
  have hmono : MonotoneOn (fun t : ℝ≥0 => min t T) Set.univ := by
    intro s hs t ht hst
    exact min_le_min hst le_rfl
  have hmap : MapsTo (fun t : ℝ≥0 => min t T) Set.univ (Icc (0 : ℝ≥0) T) := by
    intro t ht
    exact ⟨zero_le, min_le_right t T⟩
  have hbound :
      eVariationOn (fun t : ℝ≥0 => riskProcess X x D (min t T) ω) Set.univ ≤
        eVariationOn (fun t : ℝ≥0 => riskProcess X x D t ω) (Icc 0 T) := by
    simpa only [Function.comp_def] using
      (eVariationOn.comp_le_of_monotoneOn
        (fun t : ℝ≥0 => riskProcess X x D t ω)
        (fun t : ℝ≥0 => min t T) hmono hmap)
  change eVariationOn
    (fun t : ℝ≥0 => riskProcess X x D (min t T) ω) Set.univ ≠ ⊤
  exact ne_top_of_le_ne_top (hω T) hbound
