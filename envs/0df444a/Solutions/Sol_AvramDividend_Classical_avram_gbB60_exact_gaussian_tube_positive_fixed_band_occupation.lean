-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB60_exact_gaussian_tube_positive_fixed_band_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:47:36.782667+00:00
-- url     : https://prove2.me/submissions/571b9f17-252c-4a1b-938d-677e11c5c8b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB50_original_barrier_upperstrip_occupation_exact_on_tube
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- At the actual fixed-band positive Gaussian tube the omitted occupation is strict. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hTube : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |X.X s ω| ≤ (1 / 400 : ℝ)) :
    0 <
      (∫ t in Ioo (0 : ℝ) (1 : ℝ),
        if t < (1 / 1000 : ℝ) ∧
          (5 / 44 : ℝ) <
            riskProcess X (1 / 8 : ℝ)
              (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
              (Real.toNNReal t) ω
        then (1 : ℝ) else 0 ∂volume) := by
  have h :=
    avram_gbB50_original_barrier_upperstrip_occupation_exact_on_tube
      X 1 (1 / 1000 : ℝ≥0) (by norm_num) (by norm_num) ω hTube
  norm_num at h ⊢
  simpa only [h] using (show (0 : ℝ) < 1 / 1000 by norm_num)
