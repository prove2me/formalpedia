-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_stopped_negative_levy_mark_genuine_ruin_crossing_count_at_most_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:20:02.029652+00:00
-- url     : https://prove2.me/submissions/77e48c74-7d66-4644-afd0-082d99344261

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_stopped_genuinely_negative_reserve_times_subsingleton
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
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    ({t : ℝ≥0 |
      0 < t ∧ (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      X.X t ω < Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ∧
      riskProcess X x D t ω < 0} : Set ℝ≥0).encard ≤ 1 := by
  apply Set.encard_le_one_iff_subsingleton.mpr
  intro a ha b hb
  have hUnique :=
    avram_bva_a22_original_stopped_genuinely_negative_reserve_times_subsingleton
      X x D ω
  apply hUnique
  · exact ⟨ha.1, ha.2.1, ha.2.2.2⟩
  · exact ⟨hb.1, hb.2.1, hb.2.2.2⟩
