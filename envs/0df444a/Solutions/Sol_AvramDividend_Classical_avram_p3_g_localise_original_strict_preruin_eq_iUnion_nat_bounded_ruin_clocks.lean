-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_strict_preruin_eq_iUnion_nat_bounded_ruin_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:30:43.677955+00:00
-- url     : https://prove2.me/submissions/8a1d857f-df9a-4f77-9139-6755411259a3

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

/-- Source-exact strict pre-ruin exhaustion by countably many bounded
original clocks, including infinite ruin and time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ({p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) < ruinTime X x D p.2} :
      Set (ℝ≥0 × Ω)) =
      ⋃ n : ℕ,
        {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) <
            (((min (ruinTime X x D p.2) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal) : ℝ≥0∞)} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hRuin
    obtain ⟨n, hn⟩ :=
      ENNReal.exists_nat_gt (show (p.1 : ℝ≥0∞) ≠ ⊤ from ENNReal.coe_ne_top)
    have hTime : p.1 < (n : ℝ≥0) := by
      exact_mod_cast hn
    have hClock :=
      (avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
        X x D (n : ℝ≥0)).1 p.2 p.1
    exact ⟨n, hClock.mpr ⟨hRuin, hTime⟩⟩
  · rintro ⟨n, hStopped⟩
    exact (((avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
      X x D (n : ℝ≥0)).1 p.2 p.1).mp hStopped).1
