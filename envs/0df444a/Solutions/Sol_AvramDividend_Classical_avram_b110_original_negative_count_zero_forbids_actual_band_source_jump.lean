-- Prove2me | solution 1 for AvramDividend.Classical.avram_b110_original_negative_count_zero_forbids_actual_band_source_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:48:07.459064+00:00
-- url     : https://prove2.me/submissions/57552f80-60d6-4243-891d-f78815eac91c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An empty original Poisson negative cutoff rectangle contains no actual source negative-band physical jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t) (n : ℕ)
    (hZero :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0) :
    ∀ u : ℝ≥0, s < u → u ≤ t →
      ¬ (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))) := by
  intro u hsu hut hBand
  have hNonzero :=
    (avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
      X ω s t hst n).mpr ⟨u, hsu, hut, hBand⟩
  exact hNonzero hZero
