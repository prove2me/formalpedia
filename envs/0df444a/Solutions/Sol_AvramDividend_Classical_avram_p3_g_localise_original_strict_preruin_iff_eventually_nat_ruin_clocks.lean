-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_strict_preruin_iff_eventually_nat_ruin_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:42:21.560508+00:00
-- url     : https://prove2.me/submissions/c6551d68-2915-4c6f-a16e-0d577bab0571

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_preruin_eventually_nat_ruin_clocks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strict pre-ruin on the actual original Lévy path is equivalent
to eventual membership in every sufficiently long original ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ∀ (ω : Ω) (t : ℝ≥0),
      ((t : ℝ≥0∞) < ruinTime X x D ω) ↔
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (t : ℝ≥0∞) <
          (((min (ruinTime X x D ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal) : ℝ≥0∞) := by
  intro ω t
  constructor
  · exact
      avram_p3_g_localise_original_strict_preruin_eventually_nat_ruin_clocks
        X x D ω t
  · rintro ⟨N, hEventually⟩
    have hStopped := hEventually N le_rfl
    exact
      (((avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
        X x D (N : ℝ≥0)).1 ω t).mp hStopped).1
