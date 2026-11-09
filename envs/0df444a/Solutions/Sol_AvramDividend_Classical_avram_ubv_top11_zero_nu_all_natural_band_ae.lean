-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top11_zero_nu_all_natural_band_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:11:47.149854+00:00
-- url     : https://prove2.me/submissions/91454c42-c46f-4b90-8151-f4ddc5926443

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_no_negative_band_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! A single original-source probability-one event excludes every integer-horizon
negative-jump band. This is the countable step towards Gaussian continuity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0) :
    ∀ᵐ ω ∂P, ∀ N n : ℕ,
      ¬ ∃ t : ℝ≥0, 0 < t ∧ t < (N : ℝ≥0) ∧
        ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
          (nhdsWithin t (Iio t)) (nhds l) ∧
          X.X t ω + (1 / ((n : ℝ) + 1)) ≤ l := by
  apply (ae_all_iff).2
  intro N
  apply (ae_all_iff).2
  intro n
  exact avram_ubv_top11_original_zero_nu_no_negative_band_ae
    X hNuZero (N : ℝ≥0) n
