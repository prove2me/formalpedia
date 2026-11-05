-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_strict_preruin_eq_iUnion_bounded_ruin_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:23:01.444534+00:00
-- url     : https://prove2.me/submissions/447d2562-5e70-47b5-8d53-f851d09b40d0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original strict pre-ruin space-time is exactly exhausted by its
finite-horizon stopped-clock strict regions, even at infinite ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ({p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) < ruinTime X x D p.2} :
      Set (ℝ≥0 × Ω)) =
      ⋃ T : ℝ≥0,
        {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) <
            (((min (ruinTime X x D p.2) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hRuin
    let T : ℝ≥0 := p.1 + 1
    have hTime : p.1 < T := by
      dsimp [T]
      exact lt_add_of_pos_right _ (by norm_num : (0 : ℝ≥0) < 1)
    have hClock :=
      (avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
        X x D T).1 p.2 p.1
    exact ⟨T, hClock.mpr ⟨hRuin, hTime⟩⟩
  · rintro ⟨T, hStopped⟩
    exact (((avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
      X x D T).1 p.2 p.1).mp hStopped).1
