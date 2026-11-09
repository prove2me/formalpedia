-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_small13_original_zero_prestate_negative_marks_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:55:06.05456+00:00
-- url     : https://prove2.me/submissions/0c54575f-5162-49a2-bd3b-5be68b35cfe1

import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_prestate_unconditional_source_eq
import Theorems.Thm_AvramDividend_Classical_avram_bv_source14_original_zero_prejump_negative_mark_subsingleton

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- At most one original negative jump can meet the actual controlled predictable
zero prestate before or at original ruin, including infinite source activity. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Set.Subsingleton {t : ℝ≥0 |
      0 < t ∧ (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = 0 ∧
      X.X t ω < Function.leftLim (fun s : ℝ≥0 => X.X s ω) t} := by
  have hSource :=
    avram_bv_source14_original_zero_prejump_negative_mark_subsingleton X x D ω
  intro t ht s hs
  apply hSource
  · rcases ht with ⟨htpos, hclock, hzero, hjump⟩
    refine ⟨hclock, ?_, hjump⟩
    rw [avram_p3_2_original_controlled_prestate_unconditional_source_eq
      X x D hD ω t htpos] at hzero
    exact hzero
  · rcases hs with ⟨hspos, hclock, hzero, hjump⟩
    refine ⟨hclock, ?_, hjump⟩
    rw [avram_p3_2_original_controlled_prestate_unconditional_source_eq
      X x D hD ω s hspos] at hzero
    exact hzero
